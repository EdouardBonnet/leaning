# Chapter 2 Inventory: Matching, Covering and Packing

Source: `Chapter02/ch2.pdf`.

## Scope Notes

- The repository's default graph representation is `SimpleGraph V`, but
  Diestel states some Section 2.3 and 2.4 results for multigraphs. Mathlib's
  `Graph V E` is the multigraph type; Chapter 2 exposes it as the local
  abbreviation `MultiGraph V E` and adds Diestel-specific loopless/tree
  packing API on top.
- Existing Mathlib notions are reused where available:
  `SimpleGraph.Subgraph.IsMatching`, `Subgraph.IsPerfectMatching`,
  `SimpleGraph.IsVertexCover`, Hall's theorem, Tutte's theorem,
  connected components, odd components, regularity, bridges, and trees.
- Contract files contain only the intended statements as `axiom`s. Proof files
  will later restate these statements without importing contracts.

## Definitions

Already in Mathlib or Chapter 1:

- Matching: `SimpleGraph.Subgraph.IsMatching`.
- Perfect matching / 1-factor: `SimpleGraph.Subgraph.IsPerfectMatching`.
- Vertex cover: `SimpleGraph.IsVertexCover`.
- Bipartite graph: `SimpleGraph.IsBipartiteWith`.
- Odd components and Tutte violators: `SimpleGraph.oddComponents`,
  `SimpleGraph.IsTutteViolator`.
- Spanning tree, bridges, cuts, edge connectivity, factors: Chapter 1 APIs
  and Mathlib tree/connectivity APIs.
- Cycle walks: `SimpleGraph.Walk.IsCycle`.

New definitions in `definitions_ch2.lean`:

- `MultiGraph V E`: local abbreviation for Mathlib's `Graph V E`, with added
  predicates for Diestel-style looplessness, connectedness, degree, induced
  edge counts, cross-edge counts, cycle packing, tree packing/forest covering,
  quotient crossing-edge covers, and exchange chains.
- `matchingNumber`: maximum matching cardinality in a finite graph.
- `HasMatchingOf`, `neighboursIn`, `MarriageCondition`.
- `HasKFactor`: spanning `k`-regular subgraph, expressed by finite degree
  equations to avoid typeclass requirements for existential subgraphs.
- `IncidentEdge`, `Preferences`, `StableMatching`.
- `deleteVertex`, `IsFactorCritical`, `TutteCondition`,
  `DeletedComponent`, `MatchableToDeletedComponents`, `GallaiEdmondsSet`.
- `IsBridgeless`.
- `CycleIn`, `HasKDisjointCycles`, `IsCycleVertexCover`,
  `ErdosPosaCycleBound`, `erdosPosaR`, `erdosPosaS`.
- `IsVertexPartition`, `IsCrossEdge`, `crossEdgeCount`.
- `EdgeDisjointFamily`, `FamilySpanningTrees`,
  `HasKEdgeDisjointSpanningTrees`, `CanCoverEdgesByAtMostKTrees`,
  `CanCoverEdgesByAtMostKSpanningTrees`, `inducedEdgeCount`,
  `quotientGraphByPartition`, `PackingCoveringPartition`.
- `FamilyEdgeSet`, `EdgeInAtLeastTwoTrees`, `IsExchangeStep`,
  `StartsExchangeChain`, `CanImproveTreeFamily`.
- `DirectedGraph`, directed list paths, path covers, independent
  representatives.
- `IsChainFinset`, `IsAntichainFinset`, `ChainCover`,
  `maxAntichainCard`.

Ignored:

- Examples, figures, exercises, notes, and motivational text.
- Notation-only sidebars such as `G = (V,E)`, `A,B`, `CG`, `q(G)` except where
  the underlying concept is needed for contracts.

## Numbered Statements

- Theorem 2.1.1 (Konig): in a finite bipartite graph, the matching number
  equals the vertex-cover number; the formal statement includes that the
  chosen bipartition covers all vertices.
- Theorem 2.1.2 (Hall): a finite bipartite graph contains a matching of `A`
  iff the marriage condition holds.
- Corollary 2.1.3: every positive-degree regular finite bipartite graph has a
  1-factor.
- Theorem 2.1.4 (Gale-Shapley): every finite bipartite graph with preferences
  has a stable matching.
- Corollary 2.1.5 (Petersen): every finite regular graph of positive even
  degree has a 2-factor.
- Theorem 2.2.1 (Tutte): perfect matchings are equivalent to Tutte's condition.
- Corollary 2.2.2 (Petersen): every finite bridgeless cubic graph has a
  1-factor.
- Theorem 2.2.3 (Gallai-Edmonds): existence of a Gallai-Edmonds set and the
  resulting perfect-matching criterion.
- Lemma 2.3.1: a cubic multigraph of order at least `s_k` contains `k`
  disjoint cycles; the formal order is `G.vertexSet.ncard`.
- Theorem 2.3.2 (Erdos-Posa): cycles have the Erdos-Posa property.
- Theorem 2.4.1 (Nash-Williams/Tutte): tree-packing criterion by cross-edges
  of vertex partitions, counting parallel edges; the formal statement makes
  looplessness and partitions of `G.vertexSet` explicit. No nonempty
  vertex-set hypothesis is added; the local multigraph spanning-tree
  predicates handle the empty spanning edge set on the empty vertex set.
- Corollary 2.4.2: `2k`-edge-connected finite graphs have `k` edge-disjoint
  spanning trees. The Chapter 2 multigraph edge-connectivity predicate has no
  separate nontriviality side condition.
- Theorem 2.4.3 (Nash-Williams): tree covering criterion by induced edge
  counts, counting parallel edges. The formal cover uses acyclic edge traces
  in `G`, since Diestel's covering trees need not be subgraphs of `G`; the
  forest predicate forbids loops and multigraph cycles, including parallel
  2-cycles.
- Theorem 2.4.4 (Bowler-Carmesin): packing-covering partition theorem
  for multigraphs.
- Lemma 2.4.5: exchange-chain improvement lemma for a family of spanning
  trees.
- Theorem 2.5.1 (Gallai-Milgram): every finite directed graph has a path cover
  with independent representatives.
- Corollary 2.5.2 (Dilworth): in a finite poset, the maximum antichain size is
  the minimum number of chains needed to cover the poset.

## Dependencies

- 2.1.3 depends on 2.1.2.
- 2.1.5 depends on 2.1.3 and the Euler tour theorem from Chapter 1.
- 2.2.2 depends on 2.2.1.
- 2.2.3 implies 2.2.1 in Diestel's second proof.
- 2.3.1 uses the Chapter 1 logarithmic girth bound, Corollary 1.3.5.
- 2.3.2 depends on 2.3.1.
- 2.4.1 and 2.4.3 are derived from 2.4.4.
- 2.4.4 uses 2.4.5.
- Diestel derives 2.5.2 from 2.5.1; the current formal proof derives 2.5.2
  from 2.1.1 using the standard split-order bipartite graph construction.

## Proof Status

Completed proof files:

- `theorem_2_1_1.lean`: Kőnig's theorem, by Diestel's minimum-cover
  argument: weak duality by injecting matching edges into any cover, and the
  reverse inequality by splitting a minimum cover across the bipartition,
  applying Hall to the two induced `between` graphs, and joining the resulting
  disjoint matchings.
- `theorem_2_1_2.lean`: Hall's theorem, from Mathlib's Hall theorem plus the
  local `MarriageCondition` formulation.
- `corollary_2_1_3.lean`: positive-degree regular bipartite graphs have a
  1-factor, using a double-counting proof of the global Hall inequality and
  Mathlib's perfect-matching Hall theorem.
- `theorem_2_1_4.lean`: Gale-Shapley stable matching theorem.  The proof
  constructs valid finite proposal states, proves that a terminal state yields
  a stable matching, proves that every nonterminal valid state can be extended
  by one proposal, and chooses a valid state of maximum cardinality.
- `theorem_2_2_1.lean`: Tutte's theorem, directly from Mathlib's `SimpleGraph.tutte`.
- `corollary_2_2_2.lean`: Petersen's theorem that every finite bridgeless
  cubic graph has a 1-factor, using Tutte's theorem and the boundary-counting
  argument in `petersen_counting.lean`.
- `theorem_2_2_3.lean`: Gallai-Edmonds theorem. The proof chooses a largest
  maximum-defect vertex set, proves all deleted components are odd and
  factor-critical, proves the Hall matchability condition from maximality, and
  combines this structure with the fixed-set matching criterion.
- `theorem_2_5_1.lean`: Gallai-Milgram theorem. The proof uses the finite
  minimal terminal path-cover construction from `gallai_milgram_aux.lean` and
  extracts independent representatives from an inclusion-minimal terminal set.
- `corollary_2_5_2.lean`: Dilworth's theorem for finite posets, via the
  split-order bipartite graph.  A maximum matching gives a chain cover by
  source-generated chains, and Kőnig's theorem plus the corresponding minimum
  vertex cover gives the antichain bound needed to pad the cover to
  `maxAntichainCard P`.

Auxiliary proof development:

- `petersen_counting.lean`: counting reductions for Corollary 2.2.2.  It
  defines deleted-component vertex sets and boundary-edge types, proves that
  the edges incident with a set `S` in a cubic graph are bounded by
  `3 * S.ncard`, glues three boundary edges from each odd component into one
  global injection, proves that a singleton boundary edge would be a bridge,
  proves the boundary parity by pairing internal darts, and reduces the Tutte
  inequality to proving that every odd component of `G - S` has an odd,
  non-singleton boundary.
- `dilworth_aux.lean`: reusable lower-bound half of Dilworth's theorem and
  chain-cover padding.  It proves that any finite antichain injects into any
  chain cover, that every concrete antichain has size at most
  `maxAntichainCard P`, that `maxAntichainCard P ≤ n` for every
  `ChainCover P n`, and that a cover by `m` chains can be padded to a cover by
  any `n ≥ m` chains.
- `dilworth_matching.lean`: split-order graph infrastructure for Dilworth.
  It proves the split graph is bipartite, extracts an antichain from every
  vertex cover with the exact cardinal inequality, decomposes a split-graph
  matching into source-generated chains, proves the source count is
  `Nat.card P - M.edgeSet.ncard`, and proves existence of a matching attaining
  `matchingNumber`.
- `two_factor_aux.lean`: compiled infrastructure toward Corollary 2.1.5.  It
  proves that regularity transfers to Mathlib's bipartite double cover, obtains
  a perfect matching in that double cover from Corollary 2.1.3, proves that
  a bijective successor function along graph edges with no directed 2-cycle
  yields a genuine 2-factor, proves that every connected component of a
  finite `2*k`-regular graph is Eulerian using Chapter 1, and proves the
  closed-Euler-tour dart count lemmas needed to split degree `2*k` into
  indegree and outdegree `k`.
- `stable_matching_aux.lean`: compiled Gale-Shapley infrastructure for
  Theorem 2.1.4: proposal states, held edges, the held-edge subgraph, matching
  and stability extraction from terminal states, and the maximal-state
  extension lemma.
- `tree_exchange_aux.lean`: compiled infrastructure toward Lemma 2.4.5.  It
  defines single-tree replacement in a family, proves that one replacement
  preserves the spanning-tree family when supplied by an exchange step, proves
  the one-step augmentation case where the new edge lies outside the current
  family union and the removed edge occurs in another tree, and reduces a
  nontrivial exchange chain to either that one-step augmentation or a first
  replacement with unchanged family edge union and the successor edge duplicated.
- `tree_exchange_chain_aux.lean`: compiled infrastructure toward the
  minimum-chain part of Lemma 2.4.5.  It converts `StartsExchangeChain` into a
  concrete finite list chain, extracts a minimum-length chain, and exposes the
  first exchange step and suffix of a non-trivial chain.  It also proves the
  first move of the minimum-chain argument: either the first exchange already
  adds a new edge to the family union, or the first replacement preserves the
  union and moves the duplicated edge to the successor.  The file now also
  proves the full outer induction from a `StartsExchangeChain` hypothesis to
  `CanImproveTreeFamily`, conditional on the single fundamental-cycle replay
  assertion that Diestel proves using shortest exchange chains.
- `matroid_exchange_aux.lean`: compiled abstract matroid core for the
  difficult "same fundamental cycle" sentence in Lemma 2.4.5.  It proves that
  if `B - e + f` is a base and `e` is not in the fundamental circuit of `b`,
  then `b` has the same fundamental circuit after the exchange; consequently,
  a second exchange `B - a + b` commutes across the first one.
- `gallai_milgram_aux.lean`: compiled infrastructure toward Theorem 2.5.1.  It
  defines terminal sets of list-path families, proves that an independent
  terminal set supplies the representatives required by the contract, constructs
  trivial singleton path covers, selects path covers with minimum terminal count
  using `Nat.find`, and packages the contradiction from a path cover with a
  proper subset of terminals.  The current development also has a finite-ground
  `IsDirectedPathCoverOn` version for induction over a finset of vertices, plus
  compiled cover transformations for deleting a nontrivial terminal
  (`dropTerminalCover_isPathCoverOn`), deleting a singleton terminal path
  (`eraseSingletonTerminalCover_isPathCoverOn`), and extending a path by a
  deleted terminal (`extendTerminalCover_isPathCoverOn`).  It proves the
  minimality-transfer, singleton-terminal contradiction, and representative
  transfer lemmas used to close the Gallai-Milgram induction.
- `gallai_edmonds_aux.lean`: compiled infrastructure toward Theorem 2.2.3.
  It proves that factor-critical components are odd, that every component of
  `G - S` is odd for a `GallaiEdmondsSet`, and that a perfect matching forces
  `S.ncard = Nat.card (DeletedComponent G S)`.  It also proves the converse
  fixed-set construction: if `S` is a `GallaiEdmondsSet` and this cardinal
  equality holds, then the matching from `S` to the deleted components can be
  made bijective and glued to the factor-critical near-perfect matchings inside
  each component to obtain a perfect matching of `G`.  Thus the full
  perfect-matching criterion for any given `GallaiEdmondsSet` is complete.
- `gallai_edmonds_existence_aux.lean`: compiled infrastructure for the global
  existence clause of Theorem 2.2.3.  It defines the Tutte
  defect `q(G - S) - |S|`, proves existence of a largest maximum-defect set,
  proves parity lemmas for odd components and odd-order graphs, constructs the
  graph isomorphism between the project deleted-vertex model
  `delete_vertices G S` and Mathlib's `((⊤ : G.Subgraph).deleteVerts S).coe`,
  transports odd-component counts across graph isomorphisms, bridges the
  defect to `SimpleGraph.IsTutteViolator`, derives a Chapter-2 deleted-graph
  bad set from absence of a perfect matching, and proves the Hall
  characterization of `MatchableToDeletedComponents` together with its
  contrapositive.  It proves the maximality contradiction showing that a
  largest maximum-defect set has only odd deleted components, and combines
  this with the Hall obstruction to prove that such a set is matchable to
  those components.  It also provides the canonical hom `G - S → G - T` for
  `T ⊆ S`, one-vertex component-survival maps, the strict odd-component count
  increase caused by deleting a vertex from an even component, a strengthened
  even-order Tutte-surplus lemma, cardinal lemmas for lifting local sets from
  `C - c` back to the ambient graph, and the final local-to-global maximality
  contradiction proving the deleted components are factor-critical.
- `tree_packing_aux.lean`: compiled infrastructure toward Theorem 2.4.1.  It
  builds the quotient graph on partition classes from the crossing edges of a
  selected spanning tree, proves the quotient is connected, injects quotient
  edges back into selected crossing multiedges, and derives
  `P.card - 1 ≤ Nat.card {e : G.CrossEdge P | e.1 ∈ F}` for every spanning
  tree `F`.  It then sums this over a pairwise edge-disjoint family to prove
  the full forward Nash-Williams/Tutte inequality
  `k * (P.card - 1) ≤ G.crossEdgeCount P`.
- `theorem_2_4_1_forward.lean`: finalized proof of the forward implication of
  Theorem 2.4.1, importing `tree_packing_aux.lean`.  This is not the contract
  theorem file, since the reverse Nash-Williams/Tutte implication remains open.
- `multigraph_spanning_tree_aux.lean`: compiled infrastructure showing that a
  connected finite multigraph has a spanning-tree edge set in the local
  `MultiGraph.IsSpanningTree` sense.  It lifts a Mathlib simple spanning tree
  of `G.toSimpleGraph` by choosing one multiedge label per simple tree edge,
  proves the chosen labels are injective, and records the immediate
  `HasKEdgeDisjointSpanningTrees 1` consequence.  It also proves that positive
  local edge-connectivity implies `MultiGraph.Connected`.
- `corollary_2_4_2_k_one.lean`: checked `k = 1` specialization of Corollary
  2.4.2 from the positive edge-connectivity infrastructure.  The arbitrary
  `k` contract still depends on the full Nash-Williams/Tutte tree-packing
  theorem.
- `edge_connectivity_partition_aux.lean`: compiled the self-contained
  cut-counting ingredients from Diestel's proof of Corollary 2.4.2.  It
  defines the boundary of a vertex side, proves that deleting fewer than `l`
  edges cannot separate a nonempty side from a vertex outside it in an
  `l`-edge-connected multigraph, specializes this to nontrivial classes of a
  vertex partition, proves that every boundary edge of a partition class is a
  partition-crossing edge, proves the boundary-incidence double-counting
  inequality that every crossing edge is counted by at most two partition
  classes, and derives the full Nash-Williams/Tutte partition lower bound
  `k * (P.card - 1) ≤ G.crossEdgeCount P` from `2*k`-edge-connectivity.  The
  use of the reverse Nash-Williams/Tutte implication remains separate from
  this auxiliary file.
- `tree_packing_k_one_aux.lean`: compiled `k = 1` specialization of the full
  Nash-Williams/Tutte equivalence.  The reverse direction proves that if every
  vertex partition has at least `|P|-1` crossing edges, then either
  `G.vertexSet = ∅` and the empty edge set is a spanning tree, or else
  `G.toSimpleGraph` is connected: a disconnected reachable component and its
  complement form a two-class partition with no crossing edge, contradicting
  the partition bound.  This does not prove the arbitrary-`k` contract.
- `tree_packing_k_zero_aux.lean`: checked `k = 0` specializations of Theorem
  2.4.1 and Corollary 2.4.2, using the vacuous `Fin 0` family of spanning
  trees.
- `tree_packing_quotient_aux.lean`: compiled the counting step in Diestel's
  proof of Theorem 2.4.1 from Theorem 2.4.4.  If `k` quotient spanning trees
  cover all cross-edges and the Nash-Williams lower bound
  `k * (|P| - 1) ≤ crossEdgeCount P` holds, then the quotient trees are
  pairwise edge-disjoint.  This proof uses the exact non-strict inequality
  from the contract.
- `tree_packing_glue_aux.lean`: compiled the gluing step in the same proof.
  It lifts quotient edge sets back to multiedges, glues one quotient tree to
  one spanning tree inside each partition class, proves the glued edge set is
  a spanning tree of `G`, and proves the resulting family is edge-disjoint
  when the internal families and quotient family are edge-disjoint.
- `tree_packing_reverse_aux.lean`: compiled the reverse Nash-Williams/Tutte
  implication conditional on a genuine proof of Theorem 2.4.4.  It handles
  the `k = 0` and empty-vertex cases, derives connectedness from the partition
  lower bound when `0 < k`, and applies the quotient-counting/gluing
  construction to a packing-covering partition.
- `tree_packing_maximal_aux.lean`: in addition to the maximal-family setup,
  now proves that every edge in the exchange-chain set `D` is internal to the
  component partition of `(V,D)`, and therefore every edge crossing that
  partition is covered by one of the quotient traces of the chosen spanning
  trees.  The remaining Bowler-Carmesin work is to prove that the `D`-traces
  inside each component are connected spanning trees and that the quotient
  traces are quotient spanning trees.
- `tree_covering_k_zero_aux.lean`: checked `k = 0` specialization of Theorem
  2.4.3.  Covering by zero forests is equivalent to `G.edgeSet = ∅`; conversely
  the zero induced-edge inequality forces `G.edgeSet = ∅` under looplessness by
  applying the inequality to the two endpoints of any edge.
- `bowler_carmesin_k_zero_aux.lean`: checked `k = 0` specialization of Theorem
  2.4.4.  For a connected multigraph, the singleton partition
  `{G.vertexSet}` has no crossing edges, and all zero-indexed tree families are
  vacuous.
- `tree_exchange_small_k_aux.lean`: checked `k = 0` and `k = 1`
  specializations of Lemma 2.4.5.  In both cases the hypothesis that an edge
  lies in two distinct trees is impossible.
- `cycle_packing_k_zero_aux.lean`: checked `k = 0` specialization of Lemma
  2.3.1, using the vacuous `Fin 0` family of cycles.
- `multigraph_loop_degree_aux.lean`: adds the loop-aware multigraph degree
  and cycle API needed for Diestel's Section 1.10 convention: loops are
  permitted in multigraphs, contribute two to degree, and are cycles of
  length one.  This is needed for the suppression step in Lemma 2.3.1, since
  suppressing a degree-two vertex can create a loop.
- `tree_family_monotonicity_aux.lean`: compiled monotonicity API for
  edge-disjoint spanning-tree packings, induced-subgraph spanning-tree
  packings, disjoint cycle packings, and at-most-`k` forest/spanning-tree
  covers.

Lemma 2.4.5 is now proved in `lemma_2_4_5.lean`.

- The proof formalizes Diestel's minimum exchange-chain replay through an
  abstract matroid base-exchange argument, then proves the needed matroid
  exchange axiom for finite loopless multigraph spanning trees directly from
  the simple shadow of a tree.  The key graph lemma shows that replacing a tree
  edge by a chord whose endpoints lie in different components after deleting
  that tree edge preserves connectedness and the edge count.
- `#print axioms Diestel.Chapter02.lemma_2_4_5` reports only standard Lean
  axioms (`propext`, `Classical.choice`, `Quot.sound`) and no project-specific
  contract axiom.

Remaining statements still only have contracts:

- `theorem_2_4_1.lean`
- `corollary_2_4_2.lean`
- `theorem_2_4_3.lean`
- `theorem_2_4_4.lean`

The remaining proof work needs new development for Nash-Williams/Bowler-Carmesin
tree packing; this was not found as a ready-made Mathlib wrapper in the local
name checks.

## Files Created

- `definitions_ch2.lean`
- Proof files:
  `theorem_2_1_1.lean`, `theorem_2_1_2.lean`,
  `corollary_2_1_3.lean`, `theorem_2_1_4.lean`,
  `theorem_2_2_1.lean`,
  `corollary_2_2_2.lean`, `theorem_2_2_3.lean`, `lemma_2_3_1.lean`,
  `theorem_2_3_2.lean`, `lemma_2_4_5.lean`, `theorem_2_5_1.lean`,
  `corollary_2_5_2.lean`.
- Auxiliary files:
  `petersen_counting.lean`, `dilworth_aux.lean`,
  `dilworth_matching.lean`, `two_factor_aux.lean`,
  `stable_matching_aux.lean`, `tree_exchange_aux.lean`,
  `gallai_milgram_aux.lean`, `gallai_edmonds_aux.lean`,
  `gallai_edmonds_existence_aux.lean`, `tree_packing_aux.lean`,
  `theorem_2_4_1_forward.lean`, `multigraph_spanning_tree_aux.lean`,
  `corollary_2_4_2_k_one.lean`, `edge_connectivity_partition_aux.lean`,
  `tree_packing_k_one_aux.lean`,
  `tree_packing_k_zero_aux.lean`, `tree_covering_k_zero_aux.lean`,
  `bowler_carmesin_k_zero_aux.lean`, `tree_exchange_small_k_aux.lean`,
  `cycle_packing_k_zero_aux.lean`, `tree_family_monotonicity_aux.lean`,
  `multigraph_tree_shadow_aux.lean`, `spanning_tree_exchange_aux.lean`,
  `matroid_exchange_aux.lean`, `matroid_tree_exchange_chain_aux.lean`,
  `tree_packing_maximal_aux.lean`.
- Contract files:
  `theorem_2_1_1Contract.lean`, `theorem_2_1_2Contract.lean`,
  `corollary_2_1_3Contract.lean`, `theorem_2_1_4Contract.lean`,
  `corollary_2_1_5Contract.lean`, `theorem_2_2_1Contract.lean`,
  `corollary_2_2_2Contract.lean`, `theorem_2_2_3Contract.lean`,
  `lemma_2_3_1Contract.lean`, `theorem_2_3_2Contract.lean`,
  `theorem_2_4_1Contract.lean`, `corollary_2_4_2Contract.lean`,
  `theorem_2_4_3Contract.lean`, `theorem_2_4_4Contract.lean`,
  `lemma_2_4_5Contract.lean`, `theorem_2_5_1Contract.lean`,
  `corollary_2_5_2Contract.lean`.
