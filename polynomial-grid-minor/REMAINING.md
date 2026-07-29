# Remaining Work for the Degree-Ten Grid-Minor Theorem

Last audited: 2026-07-28

This file records the completed implementation plan for a self-contained Lean
proof of the exponent-ten variant of Chuzhoy--Tan Theorem 1.1.

## Target

The final theorem should have the following shape:

```lean
theorem polynomial_grid_minor_theorem_degree10 :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            polynomialGridMinorTreewidthBound10 c1 c2 g ≤ treewidth G →
              ContainsGridMinor G g
```

The threshold definition in `PolynomialGridMinorBound.lean` is complete:

```lean
def polynomialGridMinorTreewidthBound10 (c1 c2 g : ℕ) : ℕ :=
  c1 * g ^ 10 * (Nat.log 2 g) ^ c2
```

The final theorem is complete only if it uses the direct degree-ten route and
`#print axioms` reports no project axiom.

## Status legend

- `[x]` means proved and verified without a project axiom or semantic input in
  the relevant theorem closure.
- `[ ]` means not yet proved, even if a proposition or proof-data structure
  already states the desired result.
- **Partial** means useful internal lemmas exist but a named construction still
  has to be supplied.
- **Contract-backed** means the current declaration transitively uses a project
  axiom and is not evidence of closure.

## Audit baseline

- [x] The standalone import graph is complete and acyclic.
- [x] No `sorry`, `admit`, `unsafe`, or `partial` declaration was found.
- [x] Legacy contract axioms remain declared only outside the direct
  degree-ten theorem's transitive closure.
- [x] The closed endpoint and all stable public degree-ten wrappers use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [x] The direct endpoint does not use the contract-backed degree-nine theorem.

## Exact direct frontier

The most decomposed direct theorem is
`polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching`
in `PolynomialGridMinor.lean`.

It requires nine semantic inputs. No closed theorem currently supplies all of
them:

1. `DegreeThreeTreewidthSparsifierOmega`.
2. `RoutableSetFromTreewidth`.
3. `CutWellLinkedCoreFromRoutableSet`.
4. `StrongTreeOfSetsCoreFromNodeWellLinkedCore`.
5. `StrongPathOfSetsFromLeafyStrongTreeOfSets`.
6. `AppendixA3ClusterSplitInput`.
7. `Section4WeakToStrongAssemblyInput10`.
8. `LocalRoutingClusterInput`.
9. `StitchingInput`.

The work packages below close exactly this list.

## Minimal dependency route

```text
Chekuri--Chuzhoy A.2 source results
             +
degree-three sparsifier A.1
             +
Chuzhoy Theorem 6.3 / Chuzhoy--Tan A.3
             |
             v
Chuzhoy--Tan Theorem 2.3: hairy path-of-sets
             |
             v
Section 4 exponent-ten crossbar dichotomy
             |
             +------------------------------+
             |                              |
             v                              v
strong path-of-sets -> grid       all crossbars -> expander -> grid
             |                              |
             +---------------+--------------+
                             v
                 degree-ten final arithmetic
```

Chuzhoy--Tan Section 5 is not in this graph.

## Parameter ledger

The formal proof does not need the best logarithmic exponent, but it must
preserve the following scale relationships.

- Section 4 assumes an internal power-of-two parameter `q` and
  `kappa >= 2^22 * q^10 * log q`.
- The pseudo-grid depth is `D = 64 * q^4`.
- The number of slices is `M = 8 * q^4 * log q`.
- The selected weak path-of-sets system has length and width `q^2`.
- Two boosts and the linking step retain at least a constant multiple of
  `q^2`; the paper's explicit bookkeeping gives `9 * q^2 / 12800`.
- The all-crossbar branch produces a grid of side
  `Omega(q / log(q)^(3/2))`.
- Taking `q = Theta(g * log(g)^(3/2))` makes both branches contain a target
  `g`-grid.
- Theorem 2.3 is invoked with width
  `2^22 * q^10 * log q` and length `Theta(log q)`, giving a sufficient final
  threshold `O(g^10 log(g)^(beta + 64))` for its unspecified exponent `beta`.

The existing `ParameterChoice10` and canonical coefficient proofs already
perform the Lean-level rounding and domination argument.

## Work package 0: standalone project and trust harness

Status: **Complete, infrastructure**

Output: a reproducible build and a permanent axiom audit for the direct target.

- [x] Add `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`, making
  this directory an explicit standalone library.
- [x] Pin Lean `v4.30.0-rc2` and Mathlib revision
  `ff96409d623285fbfe777cf47c50574f05f63a3d`.
- [x] Remove the unused external contraction import from
  `TreewidthContract.lean`; the local treewidth API now depends only on
  Mathlib.
- [x] Make `PolynomialGridMinor.lean` compile as the aggregate target.
- [x] Add `AxiomAudit.lean` with `#print axioms` for the direct degree-ten
  endpoint and the current public theorem.
- [x] Run a fresh full build in the newly created local Lake build tree.

Acceptance criterion: `cd polynomial-grid-minor && lake build` succeeds and the
trust audit can be rerun with one documented command.

Verified on 2026-07-16. `lake build` completed 3,563 jobs, and
`lake env lean AxiomAudit.lean` reports only `propext`, `Classical.choice`, and
`Quot.sound` for the direct endpoint. The current public wrapper still reports
the four contract axioms listed above, as expected until final integration.

## Work package 1: Chekuri--Chuzhoy A.2

Status: **Complete**

Source: `chekuri-chuzhoy.pdf`, preprint Theorem 3.4; equivalently
`chekuri-chuzhoy-2.pdf`, journal Theorem 3.5.

Output: a theorem proving `ChekuriChuzhoy.TheoremA2SourceInputs` without
semantic assumptions. The final arithmetic from these inputs to a strong
path-of-sets system is already proved in `ChekuriChuzhoyTheorem221.lean`.

### 1A. Routable terminals from treewidth

- [x] Prove `RoutableSetFromTreewidth`. The axiom-free endpoint is
  `routableSetFromTreewidth_proved`, with constants `(9, 1, 1, 1)`.
- [x] Replace the Reed/Lemma 3.2 producer on the direct route. The proof uses a
  maximum global `NodeWellLinkedIn` set, minimum balanced separations, and a
  recursive tree decomposition with root capacity `8k` and bag capacity
  `9k`. The resulting theorem is
  `exists_nodeWellLinked_treewidth_le_nine_mul_card`.
- [x] Prove the missing recursive tree-decomposition infrastructure: joining
  trees, gluing region decompositions across a vertex separation, converting
  a full-region decomposition to `TreeDecomposition`, the strict-child and
  child-root arithmetic, and well-founded recursion on region cardinality.
- [x] Convert the paper's equal-cardinality node-well-linked predicate to the
  repository's maximum-packing predicate by trimming the larger side. This is
  `NodeWellLinkedIn.of_paperNodeWellLinkedIn`.
- [x] Retain the conditional paper-literal reduction with constants
  `(4, 1, 1, 1)`. Given its stronger overlapping-subset producer,
  `exists_routableSetFromTreewidth_of_large_paperNodeWellLinked` proves the
  terminal cardinality, exact trimming, and logarithmic congestion bound. It
  is not used by the completed factor-nine direct route.
- [x] The packing-to-flow part of that step is proved:
  `OrientedPathFlow.ofPathPacking_isUnitFlow_and_vertexCongestionAtMost_one`
  establishes exact endpoint loads and congestion one, and
  `NodeWellLinkedIn.toRoutableSetIn` packages every balanced bipartition.
- [x] Verify the graph monotonicity and logarithmic/cardinality side
  conditions in the exact local definition: the compiled reduction uses
  terminal monotonicity, `κ ≤ T.card`, `log₂ k ≥ 1`, and the explicit
  `NodeWellLinkedIn.toRoutableSetIn` congestion-one construction.

WP1A is complete. The old paper-literal contract axiom
`TreewidthSparsifier.lemma32_exists_large_nodeWellLinked` remains declared for
the exact overlapping-subset statement, but it is no longer used by the
direct route. The direct proof uses the weaker node-well-linked predicate that
is exactly sufficient for routability and has an axiom-free closure.

### 1B. Cut-well-linked low-degree core

- [x] Prove `CutWellLinkedCoreFromRoutableSet`. The axiom-free endpoint is
  `exists_cutWellLinkedCoreFromRoutableSet_proved`, with constants
  `(cRound, 1, 2 * cRound, 1)` for the universal positive cut-matching round
  constant `cRound`.
- [x] Repair its false proof-facing interface: require even `kappa`, and make
  both maximum degree and reciprocal well-linkedness scale with routing
  congestion `eta`. Also require `kappa <= k`, which is necessary to replace
  the source's `log(kappa)` round bound by `log(k)`. The composition derives
  this comparison from its threshold inequality and absorbs `eta` into its
  polylogarithmic constants and exponents.
- [x] Formalize the cut-matching selection used in the proof of
  Chekuri--Chuzhoy Theorem 2.21. The implementation uses the stronger local
  deterministic cut-matching theorem, preserving exact responder provenance,
  and therefore bypasses the source's randomized AARV repetition.
- [x] Produce integral routed matching paths, or prove an integral realization
  theorem before bounding the degree of the union of path supports. Rational
  weighted congestion alone does not bound support degree. `RoutableSetIn`
  now records a `PerfectPathPacking` for every balanced terminal partition;
  the completed WP1A producer supplies this stronger certificate.
- [x] Construct the same-vertex subgraph, prove its polylogarithmic degree
  bound, and produce the cut-well-linked terminal set of unchanged size.
- [x] The final cut-well-linked to node-well-linked boost is already proved by
  the local Theorem 2.14 formalization.

WP1B is complete. `RoutedCutMatchingSupport` realizes every transcript round
by node-disjoint paths, bounds the union's degree by twice the round count,
and transfers half-expansion to scaled edge-well-linkedness with denominator
twice the round count. `WellLinkedComponent` proves that the nonempty terminal
set lies in one connected component, where the same cut inequalities hold.
The producer then weakens both bounds to the contract's
`eta * log_2(k)` scale.

### 1C. Strong tree-of-sets core (closed at exponent 24)

- [x] Prove the accepted exponent-24 endpoint
  `StrongTreeOfSetsCoreFromNodeWellLinkedCore24`, corresponding to the
  Chekuri--Chuzhoy Sections 4.3--4.5 construction. The proof-producing theorem
  is `strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved`, with explicit
  parameters `buildConstant24`, log exponent `5`, and degree exponent `10`.
- [x] Produce the meta-tree, disjoint clusters, interface sets, and connector
  path families with the required width.
- [x] Record the source Theorem 4.3 bandwidth invariant in
  `BandwidthTreeOfSetsSystem`, including inheritance by one, two, or three
  incident interfaces.
- [x] Prove coherent restriction of an ordinary tree-of-sets system using one
  canonical index set per unoriented meta-edge. `StrongRestrictionData` now
  derives both connector orientations, cluster avoidance, and mutual
  connector disjointness.
- [x] Prove the graph-theoretic two-stage strongification producer
  `exists_strongTreeOfSetsSystem_of_bandwidth`. It applies the proved
  Theorem 2.14 at both connector endpoints and the scaled linked-subsets
  theorem inside each cluster; all rounding losses are explicit hypotheses.
- [x] Formalize the finite Section 5 clustering vocabulary: partitions,
  original cross-block edges, truncated bandwidth and violating cuts,
  acceptable/good clusterings, natural-valued potentials, and generic finite
  potential descent in `ChekuriChuzhoySection5Clustering.lean`.
- [x] Prove the source-sharp Corollary 2.8/2.12 grouping step. The direct
  two-stage fallback currently loses three powers of the bandwidth ratio;
  retaining the source's additional `m^4` loss requires the grouping argument
  and its constant-well-linked selected union. The cut-counting implication,
  colored Hall representative theorem, and exact block-quota conclusion are
  now proved in `ChekuriChuzhoyCorollary28.lean` and
  `ChekuriChuzhoyCorollary28Grouping.lean`. Observation 2.13 is complete from
  a `TreeGrouping`, including the Hall quotas. The remaining producer is the
  general Observation 2.12 rooted-tree pruning step that constructs the
  connected, edge-disjoint grouping. Its one-group base case, recursive
  family invariants, strong-induction descent, and conversion to
  `TreeGrouping` are proved. The formerly missing lowest-heavy selection and
  residual pruning step are now supplied by
  `hasResidualPruningStep_of_connected`; the public producer is
  `exists_treeGrouping_of_connected` in
  `ChekuriChuzhoyRootedTreeGrouping.lean`.
- [x] Complete the source-specialized journal Section 5 Claims 5.3--5.19
  needed by the exponent-24 endpoint: bandwidth decomposition,
  dense low-boundary selection, terminal path skeleton, good-router family,
  simultaneous routing, bounded-degree support tree, and final bandwidth-tree
  assembly. The dense-partition finite-moment reduction, exact finite first
  and second internal-edge moments, routing-or-cut
  dichotomy, exact bounded-group selection, and terminal-skeleton data model
  are proved. The Hind--Oellermann deletion/contraction alternative is now
  proved by `hindOellermannDeletionContraction` in `HindOellermann.lean`.
  Its proof uses the capacity-expanded named-edge incidence graph, the local
  finite vertex-Menger theorem, exact deletion/contraction cut transport, and
  the paper's double-hit counting argument. Mader admissible split-off is now
  fully proved by `maderAdmissiblePair` in `MaderTheorem.lean`.
  Named-multigraph terminal element cuts, canonical cut equivalence, deletion
  and contraction transport with the sharp one-unit fallback, and contracted
  walk provenance are now proved in
  `ChekuriChuzhoySection5ElementConnectivity.lean`. The exact no-loss
  alternative is closed in `HindOellermann.lean`. General loop-discarding
  split-off, including parallel pairs with the same other endpoint, exact degree
  reduction, admissibility semantics, and original-walk provenance are proved
  in `ChekuriChuzhoySection5SplitOff.lean`. The dangerous-set criterion,
  skew-supermodular surplus uncrossing, tight-set contraction, minimum
  dangerous-cover argument, even decomposition, and odd three-edge reduction
  close Mader's admissible-pair existence theorem without project axioms.
  The general-purpose `Theorem512Statement` interface remains outside the
  direct endpoint, but its required source-specialized routing data is produced
  by the concrete terminal skeleton and restoration modules used below.
  Claim 5.9 is complete: `claim59MomentHypotheses_of_pendantTerminals` derives
  the incidence moments, `thirteen_mul_cube_mul_claim59SourceDegreeCap_lt`
  discharges the numerical inequality, and
  `exists_densePartition_of_pendant_source_parameters` is the source-parameter
  producer. The legal contracted named multigraph is also concrete:
  `legalContracted_degree_eq_originalBoundary_card` preserves every original
  cross-block edge copy and identifies contracted degree with the source
  cluster boundary.
- [x] Prove the quantitative Hind--Oellermann/doubling/Mader core used inside
  Theorem 5.12. `exists_terminalConnectivityDegreeOutput` produces a terminal-
  labelled named multigraph with edge connectivity `2 * mu` and terminal
  degree at most twice the input degree.
- [x] Supply the Theorem 5.12 host realization consumed by the direct
  exponent-24 endpoint. The terminal skeleton, history-group provenance,
  restoration, endpoint-congestion, and one-per-group disjointness are
  produced by the concrete Section 5 assembly. The broader standalone
  `IsTheorem512Output` interface is not part of the direct theorem's closure.
- [x] Produce `GoodRouterFamily`. Claims 5.9 and 5.10 create pairwise-disjoint
  seed regions. `ChekuriChuzhoySection5PartitionAction.lean` proves the
  PARTITION action, and
  `ChekuriChuzhoySection5Theorem511Phase.phase_good_drop_or_goodRouterFamily`
  combines bandwidth normalization, finite edge-Menger, SEPARATE, and
  source-potential descent. The public producer no longer uses the former
  failed-router deletion contract.
- [x] Finish Phase 1 and Phase 2 after router production, including
  Observation 5.18 and Claim 5.19. The Singh--Lau theorem used by Claim 5.19
  is now proved by
  `SimpleGraph.SinghLau.boundedDegreeSpanningTree_proved`.
- [x] Prove the flow-chain and integrality core of Phase 1, Claims 5.14 and
  5.15. `ChekuriChuzhoySection5Phase1Bundle.lean` now obtains an exact-width,
  endpoint-injective bundle on every support edge from one global
  `SupportBundleTransversal`, routes between consecutive boundary sets inside
  each intermediate bandwidth router, and recursively realizes every finite
  injective support-tree order. The canonical-tree endpoint derives these
  orders from unique root paths and proves that strict internal path vertices
  avoid all selected routers because those routers have tree degree one. The
  common-budget family permits root-to-leaf paths of different lengths. The
  source-faithful wrapper allows every leaf flow to use a different
  width-sized boundary subset of the common root router.
  `claim514_claim515_of_supportTree_leafFamily` scales those chains and invokes
  the proved replicated-network integrality theorem, pruning the full selected
  leaf routers rather than only their boundary subsets.
- [x] Compose Claims 5.14/5.15 with host-path restoration and exact endpoint
  thinning. The producer
  `exists_restoredLeafPackingFamily_of_supportTree_leafFamily` carries the
  integral network paths back to the host, applies the maximum-degree
  multiplicity bound, and returns exactly `q` globally node-disjoint paths per
  selected router with distinct leaf-side and root-side endpoint sets.
- [x] Complete the remaining global Phase 1 assembly around the proved
  Claims 5.14/5.15. The specialized Corollary 2.12 extraction inside the root
  router is now proved by
  `exists_rootExtraction_of_truncatedBandwidth`. First-root-hit normalization
  and the complete leaf--root--leaf splice are proved in
  `ChekuriChuzhoySection5Phase1Concatenation.lean`;
  `exists_leafPairRoutingPackage_of_restored` returns exact-width perfect
  all-pairs packings whose internal vertices avoid every selected leaf router,
  and whose endpoint sets lie in the corresponding router interfaces.
  `exists_bufferedSupportPath_or_leafSelection` proves the finite-tree
  long-path/many-leaves dichotomy and constructs an injective leaf family with
  a separate root in the Case-2 branch.
  `exists_leafPairRoutingPackage_of_supportTree_leafFamily` now also constructs
  the global history-group transversal from the group-size and bundle bounds.
  `exists_bufferedSupportPath_or_leafPairRoutingPackage` composes the connected
  heavy support, spanning tree, simultaneous bundle lower bound, finite-tree
  dichotomy, and complete Case-2 routing; its other branch is the explicit
  Case-1 buffered support path.
  `ChekuriChuzhoySection5CoreAssembly.lean` instantiates the natural and
  rational parameters and connects the routing package to Phase 2 pruning.
- [x] Prove the numerator-one scaled-well-linked flow primitive needed by
  Phase 1. `ScaledWellLinkedPathFlow.lean` replaces every original edge by
  `D` integral channels, applies finite edge-Menger, projects the resulting
  full packing back to the original graph, and proves exact unit endpoint
  loads and rational edge congestion at most `D`. The public producer is
  `CapacityExpansion.exists_unitFlow_of_scaledEdgeWellLinked_one`.
  `ChekuriChuzhoySection5Phase1Flow.lean` now also transports the integral
  packing through the induced router and reindexes it to `Fin width`;
  `exists_synchronizedRouting_of_truncatedScaledBandwidth_one` is the
  source-facing producer with congestion `D` and paths contained in the
  router.
- [x] Assemble the selected skeleton paths along the degree-three auxiliary
  spanning tree into the ordinary `BandwidthTreeOfSetsSystem`, with the source
  `m^19` width loss.
- [x] Add the degree-one pendant-terminal normalization and transport the
  terminal-free output clusters and connectors back to the original graph.
  The pendant graph, degree bounds, terminal node-well-linkedness lift,
  packing augmentation, and old-copy projection are proved in
  `ChekuriChuzhoyPendantTerminals.lean`. `ChekuriChuzhoyPendantTransport.lean`
  strips leaf endpoints, projects connector packings, and reconstructs both
  ordinary and strong tree-of-sets records when output clusters avoid leaves.
- [x] Prove cluster strongness and the accepted
  `m^24`/degree/polylog threshold used by the exponent-50 composition.
  The compiled Section 5 route pays one additional factor `m` for the generic
  root-to-leaf congestion sum; this is the user-approved WP1C endpoint.
  `exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp` now performs the
  coherent canonical restrictions in two bipartition passes and proves that
  first-pass strongness survives the second. Its explicit arithmetic
  hypotheses record the two grouping/extraction/linking losses.

The completed WP1C support endpoints are imported by `PolynomialGridMinor.lean`,
including the source-sharp strongification, minimal host, host-edge bridge,
Phase 1 support, restoration, flow, endpoint-thinning, bundle-composition,
root-extraction, and all-pairs concatenation modules. The aggregate also
imports the generic rational flow-composition API
and the numerator-one scaled-well-linked integral routing producer. The focused
audit covers restriction, scaled linkedness, strongification,
finite potential descent, grouping consequences, pendant normalization,
dense partitioning, the terminal-skeleton producer, the Hind--Oellermann
deletion--contraction theorem, Mader's admissible split-off theorem, and both
capacity-expansion endpoints, the terminal-subset form of Claim 5.15, the
varying-root-boundary form of Claim 5.14, exact support-bundle thinning, finite
and canonical support-tree-path realization, the combined Claim 5.14/5.15
endpoint, and restored exact leaf-packing production.
Its last verified run
reported only `propext`, `Classical.choice`, and `Quot.sound`; rerun the
aggregate build after each newly imported support module.

### 1D. Many-leaves extraction

- [x] Prove `StrongPathOfSetsFromLeafyStrongTreeOfSets`, the DFS/many-leaves
  branch of Chekuri--Chuzhoy Theorem 4.6. The proof-producing theorem is
  `strongPathOfSetsFromLeafyStrongTreeOfSets_proved`.
- [x] The finite meta-tree dichotomy is proved.
- [x] The buffered long-path branch is proved in `TreeOfSets.lean`.
- [x] Construct the global routed DFS state by recursion over the rooted
  meta-tree. The proof handles one- and two-child nodes, reserves disjoint
  connector blocks, joins the recursively produced path systems, and casts the
  root length to the selected-leaf cardinality.

Acceptance criterion: prove a declaration of type
`ChekuriChuzhoy.TheoremA2SourceInputs` and check that its axiom closure contains
no project axiom. This is met by `theoremA2SourceInputs_proved`; the checked-in
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Work package 2: degree-three treewidth sparsifier A.1

Status: **Complete**

Source: `treewidth-sparsifier.pdf`, Theorem 1.1.

Output: an axiom-free existential proof of
`DegreeThreeTreewidthSparsifierOmega`.

The historical contract-backed threshold composition uses three axioms from
`TreewidthSparsifierContract.lean`:

1. `theorem33_treewidth_of_scaledWellLinked`.
2. `theorem34_strongPathOfSets_from_treewidth`.
3. `theorem51_degree3_wellLinked_minor_from_strong_pathOfSets`.

The proved WP2 endpoint bypasses all three through the local strong
path-of-sets route.  The unrelated contract axioms remain only as statement
documentation.

- [x] Replace the current general Theorem 3.3 interface with a true statement.
  `theorem33_treewidth_of_scaledWellLinked` is false at `Delta = 0`; specialize
  it to the only composition call (`Delta = 3`, numerator `1`) or require
  `0 < Delta`, then prove the semantic treewidth lower bound.
  `theorem33_unit_treewidth_of_scaledWellLinked` proves the required
  specialization with constant `8`.
- [x] Handle disconnected graphs and the remaining small/degenerate parameter
  cases after imposing the missing positive-degree hypothesis.  The bramble
  proof works component-independently, and the threshold/Omega composition
  treats `t = 0` and the low-threshold branch explicitly.
- [x] Supply Theorem 3.4. Prefer adapting the completed work package 1 output
  to the local path-of-sets predicates rather than independently formalizing
  the same Chekuri--Chuzhoy theorem twice.  This is
  `theorem34_localStrongPathOfSets_from_treewidth`.
- [x] Decide whether Theorem 5.1 genuinely requires the stronger
  `PaperStrongPathOfSetsSystem`. If not, restate the proof-facing theorem for
  the local `StrongPathOfSetsSystem` and avoid proving irrelevant overlapping
  terminal-subset machinery.  The construction uses only the local structure.
- [x] Prove the semantic Theorem 5.1 construction: a sufficiently wide strong
  path-of-sets system yields a degree-three terminal-respecting topological
  minor with a polylogarithmically well-linked terminal set.  The proved
  theorem
  `theorem51_degree3_wellLinked_subgraph_from_localStrongPathOfSets`
  gives the stronger same-vertex subgraph conclusion, with a `log^2` width
  requirement and a `log^8` well-linkedness denominator.
- [x] The final numerical composition of Theorems 3.3, 3.4, and 5.1 into the
  sparsifier threshold is proved.
- [x] Convert the proved threshold form to the existential Omega form required
  downstream, including the low-treewidth branch and natural-number rounding.
  `degreeThreeTreewidthSparsifierOmega_of_threshold_proved` uses constant
  `2*cSparse` with the same log exponent; its low branch constructs a one-edge
  subgraph of positive treewidth.
- [x] The support-graph conversion from a topological minor to the downstream
  degree-three graph is proved in `DegreeThreeStrongPathOfSetsContract.lean`.

Algorithmic success probability, running time, and the paper's vertex-count
bound are not required. Prove the finite existential witnesses directly.

Acceptance criterion: met by
`SimpleGraph.DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_proved`.
The checked-in audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  Verification:

```bash
lake build «statements-and-proofs».TreewidthSparsifierTheorem11
lake build AxiomAudit
```

## Work package 3: Chuzhoy Theorem 6.3 / Appendix A.3

Status: **Complete**

Source: `improved-bounds-chuzhoy.pdf`, Theorem 6.3 and Section 7, "Parallel
Cluster Splitting".

Output: an axiom-free theorem producing
`HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput cSplit` for some positive
constant `cSplit`.

The former documentary blocker is resolved. The paper gives the complete
proof, and only the `d = 3` specialization is needed.

### 3A. Minimal edge subgraph and deletable-edge lemma

- [x] Prove Observation 7.1: the union of the two terminal sets is
  `1/3`-well-linked. This is
  `AppendixA3ClusterSplit.observation_7_1_union_scaledEdgeWellLinkedIn`.
- [x] Choose an edge-minimal subgraph preserving this well-linkedness.
  `exists_edgeMinimalScaledWellLinkedSubgraph` returns `H <= G` and proves
  that deleting any edge of `H` destroys the scaled well-linkedness property.
- [x] Transfer the complete split-data record from a same-vertex minimal
  subgraph back to the original graph. This is
  `AppendixA3ClusterSplitData.mapLe`.
- [x] Isolate the edge-Menger front end of Lemma 7.2.
  `exists_exact_edgePathPacking_of_cut_lower_bound` turns a lower bound on
  every local terminal--boundary cut into an exact-size edge path packing.
- [x] Formalize the finite minimum-set choice in the proof of Lemma 7.2.
  `exists_minimumLemma72Set` chooses a smallest-cardinality `M` avoiding the
  terminals, containing at least half of `Gamma`, and with at most `gamma`
  outgoing edges.
- [x] Connect failure of the required path packing to that minimum set.
  `exists_minimumLemma72Set_of_not_hasEdgeDisjointPathsIn` applies finite
  edge Menger, takes the `Gamma`-side of the resulting cut, and identifies its
  ambient edge boundary exactly.
- [x] Prove the two cut inequalities used in Claim 7.3.
  `clusterBoundary_union_add_inter_card_le` and
  `clusterBoundary_sdiff_add_sdiff_card_le` formalize the source's
  submodularity and difference-form posimodularity inequalities.
- [x] Prove the ratio-cleared terminal arithmetic at the end of Claim 7.3.
  `gamma_mass_le_of_minimumSetConditions` derives the retained-`Gamma` mass
  bound, and `claim_7_3_gamma_arithmetic_false` closes the contradiction once
  the two cut pieces have boundary at most `gamma` and each contains less than
  half of `Gamma`.
- [x] Isolate the minimum-cardinality consequence for the two cut pieces.
  `minimumSet_partition_parts_two_mul_inter_gamma_lt` proves that a nontrivial
  partition of `M` whose two boundaries are at most `gamma` gives both strict
  half-`Gamma` bounds.
- [x] Finish Claim 7.3. `DeleteEdgeFailureCut` extracts and orients the failed
  cut after deleting an internal edge; `cut_parts_boundary_le_gamma` proves
  both new boundary bounds; and
  `delete_internal_edge_preserves_scaledEdgeWellLinkedIn` composes the cut,
  minimality, and arithmetic arguments. The terminal ratio `alpha` and the
  separate `Gamma` ratio `alpha0` remain distinct.
- [x] Prove Lemma 7.2 and produce the exact-size edge path packing.
  `AppendixA3Lemma72.lemma_7_2_edgePathPacking` proves the minimum set contains
  an edge, invokes Claim 7.3, contradicts edge minimality, and returns exactly
  `floor(alpha0 * |Gamma| / 3)` paths in ratio-cleared form.
- [x] Prove the degree-capacity and floor-arithmetic conclusion of Corollary
  7.4. `card_le_maxDegree_mul_source_card_of_staysIn` bounds an edge packing by
  `d * |T|`, and
  `corollary_7_4_scaled_boundary_bound_of_edgePathPacking` derives
  `alphaNum * |Gamma| <= 12 * kappa * d * alphaDen` from the Lemma 7.2
  packing. The packing is now supplied by `lemma_7_2_edgePathPacking`.
- [x] Define Chuzhoy's boundary vertices `Gamma(S)` and augmented boundary
  `Gamma'(S)`, and prove
  `clusterBoundary_card_le_maxDegree_mul_boundaryVertices_card`.

### 3B. Construct cluster Y

- [x] Choose the source's minimum initial set `S0` from an explicit candidate.
  `AppendixA3Lemma75.exists_minimumInitialSet_of_nodeLinked_union` uses
  minimum cardinality, which is strong enough for the required proper-subset
  contradiction, and records `rho <= 4 * |Gamma'(S0)|` without floor error.
- [x] Prove the exact augmented-boundary update after retaining one side of a
  cut. `augmentedBoundaryVertices_eq_retained_union_cut` identifies the old
  retained terminals plus new cut endpoints, and bounds those endpoints by
  the crossing-edge count.
- [x] Prove the denominator-cleared `7/8` contraction, lower-half estimate,
  deleted-edge budget update, and last-half-crossing arithmetic used in Lemma
  7.5 and Observation 7.7. These are in
  `AppendixA3Lemma75Arithmetic.lean`.
- [x] Prove termination from any graph-specific strict-shrink step.
  `AppendixA3FiniteDescent.exists_terminal_of_measure_descent` chooses a
  minimum-measure valid state, so both pruning loops can terminate without an
  executable algorithm or a finite abstract state type.
- [x] Define minimum quarter-balanced edge cuts with ratio-cleared balance,
  prove existence from an explicit candidate, and orient a minimum cut toward
  the larger retained terminal side. `AppendixA3BalancedCut.lean` deliberately
  does not claim a candidate exists for singleton terminal sets.
- [x] Construct the required candidate whenever the augmented terminal set has
  at least two vertices by selecting a half-sized subset. This is
  `exists_minimumQuarterBalancedEdgeCut_of_two_le_card`; callers must still
  discharge the visible small-cardinality case.
- [x] Prove the exact three-region edge-boundary decompositions used by both
  minimality comparisons in Lemma 2.11. The two rotated-cut cardinality
  equations are in `AppendixA3EdgeBoundaryDecomposition.lean`.
- [x] Isolate the common denominator-cleared bandwidth estimate in both cases
  of Lemma 2.11. `AppendixA3Lemma211.new_terminal_side_scaled_bound`
  produces the exact denominator `2 * alphaDen + alphaNum`.
- [x] Prove Chuzhoy Lemma 2.11 for a minimum oriented quarter-balanced edge
  cut. `minimumQuarterBalancedEdgeCut_retained_wellLinked` formalizes both
  rotated-cut cases, and the augmented-boundary wrapper yields the exact
  `alpha / (2 + alpha)` ratio.
- [x] Combine one retained-side augmented-boundary update with the
  denominator-cleared deleted-edge budget. `AppendixA3Lemma75.pruning_budget_step`
  is the graph-specific one-step inequality used by Observation 7.7.
- [x] Lift that inequality to the actual accumulated edge finset `E'` and
  preserve `E(U, S \ U) subset E'` under nested retained-side steps.
  `AppendixA3Lemma75.PruningState` now packages the exact source invariant and
  derives `8 * |E(U, S \ U)| <= |Gamma'(S)|`.
- [x] Extract and orient a sparse violating cut from failure of `1/9`
  well-linkedness, prove its retained side is a strict subset, and compose the
  resulting `PruningState` successor with finite descent. `PruningReachable`
  records an actual guarded transition history, and
  `exists_wellLinked_pruningState` returns a reachable terminal well-linked
  state with all edge-set and budget invariants intact.
- [x] Package one main Lemma 7.5 step conditional only on Observation 7.7's
  `1/8` cut bound. `minimumQuarterBalancedCut_iteration` proves inherited
  well-linkedness, `7/8` contraction, retention of at least half the old mass,
  and the next threshold bound together.
- [x] Formalize the outer finite balanced-cut iteration of Lemma 7.5 using the
  completed one-step theorem. `AppendixA3Lemma75.OuterState.exists_successor`
  proves the contracting step, and `AppendixA3Lemma75.exists_lemma75_set`
  closes the finite descent with the fixed denominator
  `finalAlphaDen = 27 * 3^128`.
- [x] Prove Observation 7.6 from Lemma 2.11. The source-facing wrapper
  `minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked_three` weakens
  the exact denominator to the next `3 * alphaDen` term.
- [x] Formalize the corrected original-terminal three-quarter crossing and
  extract the first guarded transition from `PruningReachable`. These are
  `quarterBalanced_of_three_quarter_original_crossing`,
  `retainLeft_at_three_quarter_original_crossing`, and
  `exists_guarded_original_three_quarter_crossing`.
- [x] Finish the corrected terminal-mass argument and Observation 7.7. The
  printed proof's last crossing of half the *current* augmented-boundary mass
  is invalid because new cut endpoints need not be original terminals. Track
  `|U intersect Gamma'(S)|` instead and rule out its first crossing below
  three quarters; that crossing is genuinely quarter-balanced with respect to
  the original `Gamma'(S)`. Also repair the separate zero-step case: when the
  inner pruning starts at the minimum initial set `S0`, it may already be
  `1/9`-well-linked, so the terminal state need not be a proper subset and
  minimum-cardinality alone gives no contradiction. Finite descent, actual
  edge-set accumulation, and all one-step inequalities are complete.
  `AppendixA3Lemma75.minimumQuarterBalancedCut_eight_mul_cut_le` is the
  corrected Observation 7.7.
- [x] Add the corrected outer bootstrap for the zero-step case. If `S0` is
  already small, stop. Otherwise take its first oriented minimum balanced cut
  without asserting `1/8` contraction; Lemma 2.11 makes the retained side
  well-linked, its retained original terminals give the lower mass bound, and
  quarter-balance makes it a proper subset of `S0`. Corollary 7.4 supplies a
  fresh `O(kappa*d)` upper bound. Observation 7.7 is then used only on later
  proper subsets, where minimum initiality rules out a zero-step inner loop.
  This bootstrap is the large-boundary branch of `exists_lemma75_set`.
- [x] Extract a connected cluster `Y` whose augmented boundary has bounded
  cardinality and a fixed positive well-linkedness constant for `d = 3`.
  This is `AppendixA3ConnectedCore.exists_lemma75_cluster`.

### 3C. Construct cluster X

- [x] Formalize the second finite pruning process, Lemma 7.8.
  `AppendixA3Lemma78.State.exists_strict_successor`,
  `exists_lemma78_set`, and `exists_lemma78_cluster` implement and terminate
  the process.
- [x] Use a corrected degree-three initial budget, for example
  `rho = kappa/256`: the paper bounds the augmented boundary vertices by
  `rho`, which only gives `|out(Y)| <= 3*rho`, not `rho`. The ratio-cleared
  budget is carried by `AppendixA3Lemma78.State`.
- [x] Prove its edge-budget invariant and Claim 7.9, retaining at least half of
  each original terminal set in `X`. These are the state invariants consumed
  by `exists_lemma78_set`.
- [x] Prove `X` and `Y` are disjoint connected clusters and record the exact
  augmented-boundary well-linkedness data used later. This is
  `AppendixA3Lemma78.exists_lemma78_cluster`.

### 3D. Connect and boost

- [x] Prove Observation 7.11 and Lemma 7.10, producing many node-disjoint
  `X`--`Y` paths internally disjoint from both clusters. Observation 7.11 is
  `AppendixA3Observation711.rho_le_seventy_two_mul_boundaryVertices_card`;
  the boundary-oriented Lemma 7.10 endpoint is
  `AppendixA3Lemma710.exists_lemma710_connector_boundary`.
- [x] Reuse the proved local form of Chuzhoy Theorem 2.9 /
  Chekuri--Chuzhoy Theorem 2.14 to boost endpoint and terminal subsets to
  node-well-linked sets. `AppendixA3EndpointMatching` converts the edge
  packing to the synchronized-routing interface, and
  `AppendixA3Complete.exists_clusterSplitData` applies the proved boosting
  theorem twice.
- [x] Reuse the proved small-subset linking theorem corresponding to Chuzhoy
  Theorem 2.10 / Chekuri--Chuzhoy Theorem 2.9. The final assembly applies
  `Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard`.
- [x] Prove Observation 7.12, giving `1/5` well-linkedness of the three retained
  sets in `X`. This is
  `AppendixA3ClusterSplit.observation_7_12_triple_union_scaledEdgeWellLinkedIn`.
- [x] Choose one universal natural constant `cSplit` for `d = 3`, thin all
  lower-bounded sets to exact size `w`, and prove that node-well-linkedness and
  pairwise node-linkedness survive the thinning. The explicit constant and
  all thinning/linking steps are in `AppendixA3Complete.lean`.
- [x] Package the result as `AppendixA3ClusterSplitData`, including connector
  orientation, exact endpoint sets, and internal-disjointness fields.
  `AppendixA3Complete.appendixA3ClusterSplitInput` is the axiom-free producer,
  and `AppendixA3Complete.appendixA4SplitInput` verifies its downstream
  Appendix A.4 use.

- [x] Applying the local split independently to alternate clusters and
  assembling `AppendixA4SplitData` is already proved by
  `appendixA4SplitInput_of_appendixA3ClusterSplitInput`.

Acceptance criterion: produce the existential `AppendixA3ClusterSplitInput`
required by the direct final theorem and verify the resulting Appendix A.4
theorem without a contract axiom.

Acceptance verified by
`lake build «statements-and-proofs».AppendixA3Complete PolynomialGridMinor`
and `lake env lean AxiomAudit.lean`. Both WP3 endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Work package 4: close Chuzhoy--Tan Theorem 2.3

Status: **Complete**

Output: an axiom-free `HairyPathOfSetsInput` with explicit positive constants.

- [x] Instantiate the A.1 Omega sparsifier from work package 2 using
  `DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_proved`.
- [x] Instantiate the A.2 source theorem from work package 1 using
  `ChekuriChuzhoy.theoremA2SourceInputs_proved`.
- [x] Instantiate Appendix A.3 from work package 3 using
  `AppendixA3Complete.appendixA4SplitInput`.
- [x] Appendix A.4 per-cluster assembly and the hairy/backbone disjointness
  checks are proved in `HairyPathOfSetsTheorem.lean`.
- [x] The accepted `w * ell^50 * polylog` arithmetic and source-route composition are
  proved.
- [x] Run `#print axioms` on the resulting Theorem 2.3 declaration.
  `PolynomialGridMinor.exists_hairyPathOfSetsInput_proved` depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.

Acceptance criterion: the direct theorem that obtains a degree-three hairy
path-of-sets subgraph from treewidth has no project axiom and no semantic input.

The acceptance endpoint is
`PolynomialGridMinor.exists_hairyPathOfSetsInput_proved`, defined in
`HairyPathOfSetsComplete.lean`. Verification:

```bash
lake build «statements-and-proofs».HairyPathOfSetsComplete
lake env lean AxiomAudit.lean
lake build
```

## Work package 5: Chuzhoy--Tan Section 4 assembly

Status: **Complete**

Source: `grid-minor-theorem.pdf`, Section 4.

Output: an axiom-free proof of `Section4WeakToStrongAssemblyInput10`.

The following mathematical components are already proved:

- [x] Theorem 4.1, crossbar or pseudo-grid.
- [x] Lemma 4.5, unique-linkage ordering, using Appendix B.
- [x] Theorem 4.6, slicing from the ordering.
- [x] Section 4.3 finite cleanup and intersecting-pair pruning.
- [x] Theorem 4.11, weak well-linked decomposition.
- [x] Theorem 4.15, the finite overlap-chain selection theorem.
- [x] Theorem 4.20 / Chekuri--Chuzhoy boosting theorem.
- [x] Theorem 4.21 / small-subset linking theorem.
- [x] Assembly of a weak path-of-sets system from `Section45Input`.
- [x] Assembly of a strong path-of-sets system from `StrongificationData`.

The paper-specific construction joining those components is now proved:

- [x] Correct the proof-facing pseudo-grid boundary to use the paper's
  `D = 64*q^4`, and prove
  `depth64_le_kappa_div_two_mul_g_sq_of_crossbar_threshold_degree10`. The old
  depth-one caller made the assembly input strictly stronger than the source.
- [x] Define one parameter/data record carrying `q`, `kappa`, `D`, `N`, `M`,
  slice width, retained row sets, and all proved inequalities.
- [x] Starting from the pseudo-grid returned by Theorem 4.1, perform the
  contractions and path-minimality reductions needed by the unique-linkage and
  slicing APIs.
- [x] Apply the slicing and Section 4.3 cleanup theorems and retain the exact
  row segments used by the paper.
- [x] Apply Theorem 4.11 in every slice, select the happy cluster, and prove the
  retained row-cardinality bounds.
- [x] Build `Section45Input`: selected clusters, left and right endpoint sets,
  connector packings, cluster disjointness, path disjointness, and weak
  well-linkedness.
- [x] Prove the three numerical hypotheses of Theorem 4.15 from
  `D = 64*q^4`, `N <= D*q^2`, and `M = 8*q^4*log q`.
- [x] For every selected weak path-of-sets system, apply the boost twice,
  coordinate the retained left/right indices with the connector families, and
  construct `StrongificationData`.
- [x] Apply the small-subset linking theorem with one-eighth
  thinning and prove a retained width bounded below by a universal constant
  times `q^2`. The formal natural-number bookkeeping uses the universal bound
  `ell <= 20000*w`.
- [x] Package the minor relation, length bound, width bound, `Section45Input`,
  and `StrongificationData` as `Section4WeakToStrongAssemblyInput10`.

Implement this in two reviewable producers rather than attacking the final
input at once:

- [x] `section45Input_of_pseudoGrid_depth64`: construct the depth-`64*q^4`
  slicing/cleanup output, a minor `J`, a `MaxDegreeAtMost J 4` certificate, and
  the complete `Section45Input` with its length bound.
- [x] `strongificationData_of_weakPathOfSetsSystem_maxDegreeFour`: from that
  bounded-degree weak system, construct synchronized retained nail sets and
  `StrongificationData`, with `ell <= 20000*w`.

Acceptance criterion: `CrossbarTheorem` proves the exponent-ten crossbar or
strong-path-of-sets dichotomy from no external branch input.

The acceptance endpoint is
`CrossbarTheorem.crossbar_or_strong_pathOfSets_minor_degree10_proved`, produced
from `Section4Assembly.section4WeakToStrongAssemblyInput10_proved`. The latter
uses `section45Input_of_pseudoGrid_depth64` and
`strongificationData_of_weakPathOfSetsSystem_maxDegreeFour`. The permanent
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Verification:

```bash
lake build «statements-and-proofs».Section4Complete
lake env lean AxiomAudit.lean
lake build
```

## Work package 6: strong path-of-sets to grid

Status: **Complete**

Source: `chekuri-chuzhoy.pdf`, Theorem 3.1 and Corollaries 3.2--3.3; journal
numbering differs as documented in `README.md`.

Output: axiom-free proofs of `LocalRoutingClusterInput` and `StitchingInput`.

### 6A. Local routing

- [x] Finite descent from an arbitrary linkage to a good linkage or a grid is
  proved in `ChekuriChuzhoyTheorem31.lean`.
- [x] Theorem 2.15's tree-with-many-leaves alternative is proved.
- [x] Clean auxiliary-tree paths are realized as original graph bridges.
- [x] The auxiliary-tree extraction of a pairwise-bridged subpacking is proved.
- [x] Finish Appendix B.1's page-60 rerouting proof in
  `ChekuriChuzhoyTheoremB1.lean`.
- [x] Close both the terminal sparse-grid branch and the symmetric type-two
  branch rather than stopping at another page-60 proof-data structure.
- [x] Produce `AppendixB1.TheoremB1Statement` for every required linkage.
- [x] Use the completed B.1 theorem and existing descent to prove
  `LocalRoutingClusterInput` with the exact `(16*h + 10)*q` width condition.
- [x] Resolve the width mismatch.  The sharp `p + 4` form of Theorem 2.15 is
  proved in `ChekuriChuzhoyTheorem215Sharp.lean`, and
  `ChekuriChuzhoyTheorem31Sharp.lean` now derives the exact
  `(16*h + 10)*q` local threshold.

The Appendix B.1 proof is now completed by the focused
`ChekuriChuzhoyTheoremB1*` modules.  They formalize the page-60 type split,
bump/cross descent with the strict row measure, full boundary-to-boundary
columns, hill replacement and cycle erasure with the strict non-row-edge
measure, reconstruction of row contacts from the auxiliary corridor,
preservation of bump- and cross-freeness, the blocker/valley ascent, common
column order, and the terminal sparse-grid model.  Both the type-one and
type-two majority branches use the same proved corridor theorem.

`ChekuriChuzhoyWP6Complete.lean` supplies the uniform producer
`AppendixB1.theoremB1_proved`, then closes the already proved localization and
composition chain with:

- `localRoutingClusterInput_proved`;
- `corollary32Input_proved`; and
- `strongPathOfSets_containsGridMinor_proved`.

The last theorem is the unconditional WP6 endpoint with hypotheses
`2 * g * (g - 1) <= ell` and `16 * g ^ 2 + 10 * g <= w`.
All four declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.

### 6B. Global stitching

- [x] `EvenClusterOutputs` and canonical `StitchingPieces` are defined and
  their local disjointness properties are substantially proved.
- [x] Concatenate the local even-cluster row paths through all intervening
  strong path-of-sets connectors. `StitchedPrefix.extend` supplies the general
  successor step through every local output.
- [x] Replace the hard-coded first/second/third prefixes with the general
  `stitchedPrefixNat` induction. It retains row-index maps for every start,
  local, and between piece.
- [x] Prove the resulting `stitchedRowPacking` is a path packing of cardinality
  `g` and remains in the full path-of-sets prefix region.
- [x] Prove exact row traces in every completed even one-based cluster.
  `StitchedPrefix.local_trace_eq` is preserved by the induction and
  `traceOn_evenCluster` packages the result.
- [x] Add generic `GraphPath.appendWithEq` ordering lemmas: `Before` is
  preserved in either component, and every vertex of the left component is
  before every vertex of the right component.
- [x] Strengthen the two-gap producer to retain the actual middle-cluster
  packing `Q2`, a row equivalence from the collapsed packing, and exact middle
  trace equality. `TwoGapConcatPackingData` retains the original chosen `Q2`,
  and `BetweenStitchingPackingData` plus `StitchingPieces.between_provenance`
  thread it through one combined canonical chooser.
- [x] Prove exact traces in every intervening odd one-based cluster.
  `StitchedPrefix.between_trace_eq` is preserved by the successor induction,
  and `stitchedRowPacking_traceOn_oddClusterAfterEven` packages the final
  widened result. An independent source review checked the indexing through
  the last applicable odd cluster.
- [x] Retain analogous trace provenance for the initial `leftNextPacking` in
  the first cluster. `StartStitchingPackingData` records the dependent source
  packing and row map, `StitchedPrefix.start_trace_eq` carries it through the
  induction, and `stitchedRowPacking_traceOn_firstCluster` exposes the final
  widened trace.
- [x] Prove `row_trace_cluster` for every row and every cluster.
  `clusterIndex_cases` exhausts the first/even/intervening-odd indices and
  `stitchedRowPacking_traceOn_cluster` dispatches to the exact trace endpoints.
- [x] Prove `row_clusters_ordered` by carrying the target ordering proposition
  as a prefix invariant, using the completed generic append-order API.
- [x] Transfer each even-cluster pairwise bridge family to the global rows.
  `stitchedRowPacking_hasPairwiseBridgesIn_evenCluster` lifts local bridges,
  proves internal disjointness from the entire assembled packing, and survives
  terminal widening.
- [x] Package the construction as `StitchedRows`, thereby proving
  `StitchingInput` via `stitchingInput_proved`.

- [x] Once `StitchedRows` is available, the sparse-grid certificate, grid
  model, and minor transfer in `PathOfSetsGrid.lean` are proved.

Acceptance criterion: prove the strong-path-of-sets-to-grid input used by the
direct degree-ten theorem with no Corollary 3.2 contract axiom.  This is
achieved by `strongPathOfSets_containsGridMinor_proved`.

Verification:

```bash
lake build «statements-and-proofs».ChekuriChuzhoyWP6Complete
lake env lean AxiomAudit.lean
lake build
```

## Work package 7: all-crossbar branch audit

Status: **Mathematically complete; retain a regression check**

- [x] Fixed-round cut-matching produces the required half-expander.
- [x] The auxiliary support graph has the required degree and separator bounds.
- [x] The explicit Theorem 8.1 consequence gives the target grid order.
- [x] The auxiliary graph is realized as a minor of the host hairy system.
- [x] The direct degree-ten endpoint internalizes this branch without a project
  axiom.
- [x] `FinCutMatchingGameTranscript.toRoundFamily_crossbar_at_round_cluster`
  shows that the application of
  Chuzhoy--Tan Lemma 3.3 occurs only after odd-cluster stitching has placed a
  crossbar in every matching-round cluster. This guards against accidentally
  using the under-specified printed lemma statement.

Acceptance criterion: the regression theorem and the direct endpoint continue
to report only standard Lean axioms.

## Work package 8: final integration

Status: **Complete**

- [x] Produce theorem witnesses for all nine inputs of the direct source-route
  theorem.
- [x] Instantiate the theorem in `PolynomialGridMinorComplete.lean` at the
  direct degree-ten boundary.
- [x] Add a short, closed theorem with the public target statement and a name
  that does not suggest it is conditional.
- [x] Repoint `PolynomialGridMinor.polynomial_grid_minor_theorem_degree10` and
  the compatibility wrapper in `PolynomialGridMinorContract.lean` to the
  direct closed theorem.
- [x] Do not change the degree-nine theorem or claim that it has become
  self-contained.
- [x] Run the permanent trust audit. The project-axiom list is empty.
- [x] Run a clean standalone full build.
- [x] Update `README.md` from "not yet closed" to the final proof status and
  record the exact final theorem name.

Acceptance criterion: the public exponent-ten theorem compiles in a clean
build and `#print axioms` lists only standard Lean axioms.

The proof-producing endpoint is
`SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_proved`.
It applies the expanded nine-input source frontier directly. The proof-facing
alias `SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10`,
the root alias `SimpleGraph.polynomial_grid_minor_theorem_degree10`, and the
compatibility wrapper
`SimpleGraph.PolynomialGridMinorContract.polynomial_grid_minor_theorem_degree10`
all delegate to that endpoint. Verification on 2026-07-28 used:

```bash
lake build
lake env lean AxiomAudit.lean
```

## Recommended execution order

1. Complete work package 0 so every subsequent change has a reproducible build
   and trust check.
2. Run work packages 1, 3, 5, and 6 in parallel where contributor capacity
   permits; their write scopes are largely disjoint.
3. Complete work package 2 after or alongside work package 1. Reuse A.2 for the
   sparsifier's strong-path theorem instead of duplicating it when feasible.
4. Close work package 4 once A.1, A.2, and A.3 are available.
5. Perform work package 8 after Theorem 2.3, Section 4, and the strong-grid
   branch are all closed.

The highest mathematical risks are the A.2 tree-of-sets construction, the
sparsifier Theorem 5.1 construction, Appendix B.1 local routing, and the newly
opened Section 7 cluster-splitting proof. Section 4 and global stitching are
expected to be more about dependent data assembly, but they still require
careful path-disjointness and ordering proofs.

## Explicit non-goals

- Chuzhoy--Tan Section 5 and the exponent-nine refinement.
- Algorithmic running-time formalization.
- Probability estimates not needed to extract finite existential witnesses.
- The sparsifier paper's `O(k^4)` vertex-count claim.
- Reproving both editions of the Chekuri--Chuzhoy paper.
- Eliminating every contract axiom in the directory when it is outside the
  direct degree-ten theorem's closure.
- Replacing the existing graph, path, flow, minor, or treewidth foundations
  with new APIs.

## WP1C checkpoint update (2026-07-20)

- [x] Closed the qualitative section-5 bridge from rooted leaf
  pairings to the pairwise-direct bandwidth-tree input via
  `canonicalPhase2PrunedGraph`.
- [x] Exported this bridge through `PolynomialGridMinor.lean`.
- [x] Added audit points for the two new bridge declarations in `AxiomAudit.lean`.
- [x] Arithmetic wiring is closed by the exponent-24 endpoint
  `strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved`.
- [x] Remove the Singh--Lau project dependency by proving
  `SimpleGraph.SinghLau.boundedDegreeSpanningTree_proved` and using it in
  Claim 5.17.
- [x] Remove the former CNS13 failed-router deletion dependency. The direct
  source-potential PARTITION/SEPARATE proof produces the router family without
  an edge-deletion bridge.

## WP1C source-sharp assembly update (2026-07-21)

- [x] Proved unsampled Phase-1 endpoint matching and group-size congestion in
  `ChekuriChuzhoySection5RawBundle.lean`. The many-leaves branch now retains
  all Theorem 5.10 history groups instead of paying an extra factor `n` for a
  global transversal. Exact `Fin width` routing, canonical root-to-leaf
  composition, integral extraction, restoration, and all-pairs concatenation
  are produced by `ChekuriChuzhoySection5RawLeafAssembly.lean`.
- [x] Composed the source-sharp long-path and many-leaves branches through
  good-router production, Phase 2, coarse strongification, and pendant
  projection in
  `ChekuriChuzhoySection5CoreAssembly.exists_strongTreeOfSetsSystem_of_parameters`.
  The theorem compiles with the source-sized support premise
  `n^2 * (4 * Delta * leafWidth) <= 2 * mu`; the former conservative
  `n^3` premise has been removed.
- [x] Removed the Section-5 import cycle by moving the finite meta-tree
  dichotomy to `ChekuriChuzhoyMetaTreeDichotomy.lean`.
- [x] Fixed every internal Section 5 parameter in
  `ChekuriChuzhoySection5Arithmetic.lean` and proved
  `exists_strongTreeOfSetsSystem_of_source_budgets`; only the source degree
  cap, skeleton-flow budget, and terminal-capacity budget remain in its
  statement. The many-leaves selection now retains the no-long-path
  certificate and proves every selected root-to-leaf distance is at most `m`,
  rather than bounding it by all `n = m^2` routers.
- [x] Discharge the explicit natural/rational parameters of the compiled core
  theorem from one `buildConstant24 * W * m^24 * Delta^10 * log(x)^5 < x`
  hypothesis and expose the producer
  `strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved`.
- [x] Accept the generic root-to-leaf congestion sum and its resulting extra
  factor `m`; no disjoint-zone refinement is required for the exponent-24
  endpoint.
- [x] Remove the Singh--Lau bounded-degree spanning-tree dependency from that
  closure. `SinghLauRounding.lean` proves the residual-polytope extreme-point,
  laminar uncrossing, token-count progress, and strong-induction rounding
  argument and exposes
  `SimpleGraph.SinghLau.boundedDegreeSpanningTree_proved`.
- [x] Remove the remaining external proof dependency from that closure.
  `ChekuriChuzhoySection5Theorem511Phase.lean` formalizes the numbered
  Section 5 actions and finite descent used by the source.

WP1C is complete at the user-approved exponent 24. The direct endpoint's
axiom closure contains no project-specific axiom: both Singh--Lau rounding and
the Section 5 good-router producer are proved in Lean.
