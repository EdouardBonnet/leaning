# Formalization Skills and Pitfall Avoidance

This file records working practices learned while closing the polynomial
grid-minor proof. Update it whenever an approach fails, a source mismatch is
found, or a repeatable proof pattern succeeds.

## What counts as progress

- Start from one named output in `REMAINING.md` and identify the declaration
  that must construct it.
- Progress means proving a source lemma, constructing a required data field, or
  removing a semantic hypothesis from a downstream theorem.
- Renaming an `Input`, moving a hypothesis into a structure, or adding a theorem
  that merely accepts the same proposition is interface work, not proof
  closure.
- A component is closed only when `#print axioms` shows no project axiom in its
  transitive proof and every paper-level premise has a Lean producer.

## Before writing Lean

1. Read the exact output structure or proposition and list every field.
2. Search for existing producers with `rg`; check theorem types, not names or
   comments alone.
3. Separate bookkeeping fields from semantic fields. Close the bookkeeping
   first so the remaining goal states the mathematical gap precisely.
4. Locate the source theorem and its proof, recording the paper version and
   theorem-number mapping.
5. Check that cardinalities, disjointness, graph restrictions, and logarithmic
   hypotheses match the local statement exactly.
6. Test universal numeric statements on `0`, `1`, an edgeless singleton, and
   the smallest admissible graph before proving them. A missing positivity
   premise can make a paper-inspired theorem literally false in Lean.
7. Trace each quantified parameter to its caller. If the paper needs a
   canonical value such as `D = 64*g^4`, expose that value at the producer
   boundary instead of demanding a stronger result for arbitrary `D`.
8. Check whether a routing premise becomes vacuous on odd cardinalities and
   whether every loss depends on congestion. Balanced cut-matching interfaces
   should require an even terminal count or explicitly handle a leftover.
9. When a source bound is stated using `log kappa` but a local interface uses
   `log k`, prove `kappa <= k` at that boundary. Monotonicity of logarithms is
   unavailable without the size comparison, even if the intended caller
   happens to imply it.

## Productive decomposition

- Split a paper theorem at constructions that have independently reviewable
  invariants: selected sets, path families, induced subgraphs, and final
  cardinality bounds.
- Prefer a small theorem that produces one concrete field over a large theorem
  with several new provider hypotheses.
- For existential graph constructions, first define the object, then prove
  membership/subset facts, then disjointness, then connectivity/routing, and
  only then package the structure.
- When all witnesses live on the same vertex type, add a record-level `mapLe`
  constructor once. Existing graph-monotonicity lemmas then transfer clusters,
  linkedness, path packings, and internal-disjointness back from a minimal
  subgraph without repeating field-by-field arguments at every call site.
- Keep arithmetic and graph-theoretic obligations separate. Reuse the existing
  parameter-selection layer rather than reproving asymptotic domination inside
  a source theorem.
- Compile the lowest changed module and one immediate consumer before moving
  upward.
- For a finite pruning loop, avoid committing early to an executable recursive
  state machine. Package all preserved facts in `Valid`, choose a valid state
  of minimum natural measure with `Nat.find`, and contradict minimality from
  the strict-shrink step. This separates termination from the graph-specific
  invariant proof and works even when the abstract state type is not finite.

## No-progress protocol

Apply this protocol when two consecutive attempts do not reduce the semantic
goal or when a proof grows without producing a compiling intermediate lemma.

1. Stop editing the large theorem.
2. Record the exact Lean goal and the first missing source assertion.
3. Classify the blocker as elaboration, local API mismatch, missing finite-set
   bookkeeping, or genuinely missing mathematics.
4. Split off the smallest proposition whose proof would make the parent goal
   strictly simpler.
5. Compile that proposition in isolation. If it still does not move, compare
   it against the paper statement and weaken or specialize it only when the
   downstream consumer permits this.
6. Update `REMAINING.md` and this file with the blocker instead of adding an
   assumption that hides it.

For delegated work, require the agent to return exact declaration names,
file-line references, and either a compiling patch or a smallest missing lemma.
If an agent reports only that a theorem is difficult, split its assignment by
constructor field or numbered source lemma before retrying.
- Do not delegate an open-ended source/API audit when the source already
  identifies the missing construction. For Theorem 5.10, the critical path is
  a path-realized recursive Hind reduction followed by group-preserving Mader
  split-offs; assign one transition or one invariant, not the whole audit.
- Broad "map all of Section 5" agents do not converge: the source mixes
  clustering, routing, multigraph reduction, probability, and arithmetic.
  Delegate one numbered claim or one output structure with an exclusive file
  scope. The focused pairwise-disjoint Hall-selection package succeeded under
  that discipline, while two broad Section 5 explorers produced no usable
  declaration.

## Lean-specific pitfalls

- Declarations now live under `SimpleGraph`. Generic unqualified names can
  resolve to unrelated declarations in that large namespace. Qualify fragile
  facts such as `Finset.disjoint_left` explicitly.
- Do not trust a successful compile as a trust result. Run
  `lake env lean AxiomAudit.lean` or add a focused temporary `#print axioms`.
- Contract files are statement documentation. Importing a contract theorem can
  silently reintroduce a project axiom even when the calling theorem contains
  no `axiom` or `sorry`.
- Avoid rebuilding the 59k-line Appendix B module after unrelated edits. Use a
  targeted module build during development and reserve `lake build` for
  integration checkpoints.
- Do not react to linter warnings by broad formatting or cleanup while closing
  a semantic proof obligation.
- The project uses natural-number subtraction. Prove lower bounds before
  rewriting subtractions, and make truncation cases explicit.
- When a subtype such as an incident-edge name depends on a vertex parameter,
  rewriting that vertex can make the subtype proof type-dependent and fail.
  Use `simpa only [h]` for an endpoint relation or `congrArg` for an unordered
  edge equality, rather than rewriting through the dependent subtype.
- Do not translate a real lower bound such as `rho / 4 <= |S|` as
  `rho / 4 <= S.card` over naturals: floor division weakens it in the wrong
  direction when `rho` is not divisible by four. Use the ratio-cleared form
  `rho <= 4 * S.card`, or carry an explicit divisibility hypothesis.
- A theorem name or source citation does not validate its quantifiers. The
  former general sparsifier Theorem 3.3 interface allowed `Delta = 0`, where
  its conclusion is false; specialize interfaces when that is all consumers
  need.
- Do not quote the ordinary tree-of-sets threshold as the strong-tree
  threshold. In Chekuri--Chuzhoy, Theorem 4.3 contributes `m^19`, while Lemma
  4.5 loses another `m^4` through the squared bandwidth parameter. A final
  strong width `W` therefore needs an `W * m^23` term; with `m = ell^2` and
  `W = Theta(w * ell^2)`, this is exactly the source's `ell^48` loss. The
  completed direct route deliberately uses the accepted coarser `m^24`
  endpoint and propagates the resulting `ell^50` loss.
- `edgeFinset.card` may retain incompatible inferred `Fintype` instances when
  graphs are carried through subtypes. Use `edgeSet.ncard` for minimization
  measures and strict edge-deletion counts.
- Weighted flow congestion bounds total weight, not the number of supported
  paths through a vertex. Do not infer a degree bound for the union of path
  supports without an integral routing or a separate support-congestion bound.
- For numerator-one scaled edge-well-linkedness with denominator `D`, avoid
  extracting rational paths from a real max flow. Replace each original edge
  by `D` degree-two channel vertices and attach private terminal leaves, then
  apply finite edge-Menger. Project channels by fixing one endpoint and
  deleting collapsed walk steps. Charge every retained projected edge to the
  unique non-collapsed incidence edge of its channel; edge-disjointness then
  injects all users of one original edge into `Fin D`.
- When cut-matching rounds are realized by selected path packings, retain a
  `FollowsResponder` certificate in the transcript theorem. Expansion alone
  forgets which physical packing realizes each abstract matching, so it cannot
  be charged to the support graph's cuts afterward.
- Constants intended to serve every finite terminal type must be quantified
  before that type. A theorem of shape `forall X, exists c, ...` does not
  directly produce the uniform constant required by a graph-independent
  source interface, even when its proof happens to choose the same expression.
- To localize a globally well-linked nonempty terminal set, choose the
  connected component of one terminal. A second terminal outside it would
  give a zero-edge cut with positive terminal mass on both sides; after proving
  all terminals lie in the component, the global cut inequality restricts to
  each partition of that component.
- Region containment is too weak to recover a path trace or ordering after
  repeated concatenation. If the final record needs `TraceOn` or `Before`, keep
  the constituent segment, its row-index map, and its position in the
  concatenation invariant. Discovering this only after building the full path
  forces the entire induction API to be strengthened.
- For an append-order invariant, split both cluster indices when the successor
  adds an odd connector and an even cluster. The later index alone has three
  cases, but in the new-even case the earlier index has two cases as well.
  Use the explicit `GraphPath` append-order theorem and supply the glue
  equality and `IsPath` proof when Lean cannot infer them from an untyped
  intermediate `have`.
- Edge-path packings permit zero-edge singleton paths. Any endpoint-capacity
  argument must make the source and target terminal sets disjoint; otherwise
  the index type can contain many edge-disjoint copies of the same trivial
  path and no degree bound controls the packing cardinality.
- For undirected cut submodularity, avoid choosing an orientation for `Sym2`
  edges or constructing a global injection between duplicated cut
  occurrences. Define a symmetric `0`--`1` crossing indicator with
  `Sym2.lift`, prove the sixteen endpoint-membership cases, and sum the
  pointwise inequality over the finite edge universe. Remember to use
  `G.adj_comm` in the lift's symmetry proof.
- Keep distinct source ratios distinct across a composed argument. Chuzhoy
  Claim 7.3 uses `alpha` for the original terminal set and `alpha0` for
  `Gamma`; identifying them produces a compilable but unjustifiably stronger
  theorem. Name ratio parameters by their terminal set at module boundaries.
- To prove that a minimum Menger-side set contains an edge, first inject its
  boundary vertices into unordered boundary edges. If the set were
  independent, scaled well-linkedness gives every retained terminal a
  neighbor, hence a boundary vertex. This yields `|Gamma| <= 2*gamma`, which
  directly contradicts the ratio-cleared `3*alphaDen*gamma <
  alphaNum*|Gamma|` after using `alphaNum <= alphaDen`.
- A broad build run while another worker owns and is editing a dependency can
  observe a transient noncompiling state. Do not classify that as a regression
  in the reviewed package. Wait for the owner to finish, build each changed
  target, and then run the integration build from a stable tree.
- When proving a cardinality identity after defining a local set abbreviation,
  avoid `rw` with a set equality if the same set occurs inside the right-hand
  intersections: Lean may rewrite every occurrence and distort the goal. Use
  a `calc` step with `congrArg Finset.card` and then apply
  `Finset.card_union_of_disjoint` explicitly.
- Accumulated cut sets need not be pairwise disjoint. Preserve them as the
  actual finset union and use `Finset.card_union_le` for the budget; requiring
  cardinal additivity would introduce an unnecessary and fragile invariant.
- To obtain strict vertex-set descent from a violating well-linkedness cut,
  use the strict failed cut inequality to prove the smaller terminal side is
  nonempty. A vertex on that side witnesses that the retained side is not the
  whole current set; a merely nonempty graph cut is not required.
- A state field named `deletedEdges` is not source-faithful merely because its
  type is `Finset (Sym2 V)`. Record that every member lies in `G.edgeSet` and
  that no deleted edge remains internal to the current retained set; otherwise
  arbitrary structure values admit loops and unrelated unordered pairs that
  no pruning sequence can produce.
- Utility constructors that represent paper transitions should require the
  semantic guard even when their field proofs use only a weaker inequality.
  For the Observation 7.7 transition, require both larger-side orientation and
  the strict failed `1/9` cut bound so empty and no-op cuts are unrepresentable.
- Numerical state invariants do not imply reachability. When finite descent is
  meant to terminate an iterative construction, use an inductive predicate
  generated by the initial state and guarded transition, and minimize only
  over reachable states. Taking `Valid := True` can select a vacuous empty
  structure value with no predecessor history even when every field is true.
- `lake env lean AxiomAudit.lean` reads existing imported `.olean` files and
  does not rebuild a changed aggregate import. Run `lake build
  PolynomialGridMinor` first, or directly import the changed module in a
  focused audit, before interpreting an unknown-constant audit failure.
- Arithmetic tactics do not automatically identify a local `let` abbreviation
  with the expanded expression in another hypothesis. Before calling `omega`,
  restate orientation, threshold, or cardinality hypotheses with `simpa
  [localName]`; otherwise the tactic may report an independent-variable
  counterexample even though the intended expressions are definitionally
  equal.
- Check which direction and which strength of a cited theorem the consumer
  actually needs. For WP1A, the paper's factor-four overlapping-subset
  statement was stronger than necessary: a maximum global `NodeWellLinkedIn`
  set directly supplies the disjoint-subset routing predicate with factor
  nine and avoids the paper-literal contract axiom.
- For recursive balanced-separator decompositions, keep the numerical
  invariant explicit. Extend a large region's prescribed root to cardinality
  `8*k`, use the extended root union the separator overlap as the center bag
  of cardinality at most `9*k`, pass each center-side intersection as a child
  root of cardinality at most `8*k`, and recurse on strict region cardinality.
- If a decomposition proof stalls at a monolithic gluing obligation, split it
  into independently compiling layers: tree join, region-decomposition glue,
  conversion to `TreeDecomposition`, cardinal arithmetic, and well-founded
  recursion. Audit the final producer only after those layers compile.
- For a routed cut-matching producer, split the implementation into five
  independently compiling layers: provenance-preserving transcript selection,
  logarithmic round arithmetic, support-degree bounds, abstract-to-physical
  cut charging, and connected-component localization. This keeps endpoint
  equivalence bookkeeping out of the final constant assembly.
- When restricting connectors of a tree-of-sets system, store one index set
  only in the increasing `Fin` orientation and define the opposite connector
  by reversal. Independent restrictions in both orientations create an
  unnecessary and difficult endpoint-coherence obligation.
- For tree strongification, retain the node-well-linked carrier above each
  final interface. Pairwise linkedness can then be proved from scaled
  bandwidth and carrier cardinality, while later path restrictions preserve
  node-well-linkedness by terminal monotonicity.

## Source-specific pitfalls

- The exponent-ten target uses Chuzhoy--Tan Section 4. Section 5 belongs only
  to the sharper exponent-nine result.
- Chekuri--Chuzhoy theorem numbers differ between the preprint and journal
  versions; use the mapping in `README.md`.
- Do not confuse the ordinary tree-of-sets threshold with the strong one.
  Theorem 4.3 contributes `m^19`; source-sharp Corollary 2.12 strongification
  contributes `m^4`, giving `m^23` and exactly the downstream `ell^48` term.
  Replacing Corollary 2.12 by independent Theorem 2.14 selections plus a final
  linkedness thinning loses a third bandwidth factor and yields `m^25`; that
  fallback is valid graph theory but cannot close the exponent-48 route.
- Treat fixed polylogarithmic exponents as slack for the degree-ten target.
  Do not spend proof effort matching a printed logarithmic exponent exactly
  when a larger universal constant exponent composes cleanly. This flexibility
  does not justify claiming the paper's source-sharp polynomial power. The
  completed WP1 route explicitly records its user-approved `m^24` threshold
  and the downstream `ell^50` bound.
- A statement structure is not a source-theorem producer. For Corollary 2.8,
  the cut-counting theorem from `TreeGroupedTransversal` closes only the last
  implication; closure still requires constructing the connected edge-disjoint
  tree grouping and proving the colored Hall quotas.
- Do not estimate a work package from a compressed checklist entry such as
  "Claims 5.3--5.19". Expand each claim into its witness-producing theorem,
  host/provenance transport, parameter arithmetic, and external citations,
  then mark which declarations are actually inhabited. A compiling structure,
  conditional theorem, or contract-shaped endpoint is not completed work.
- Audit citations inside proofs, not only theorem statements. Claim 5.19, for
  example, invokes the Singh--Lau bounded-degree spanning-tree theorem; that is
  a separate formal dependency even though it is hidden inside one paragraph
  of the Section 5 proof. Missing cited papers are schedule risks and must be
  listed before giving a completion estimate.
- For iterative-relaxation proofs whose support changes, keep coordinates in
  one fixed finite ambient type (`Sym2 V` here), require zero outside the
  current allowed `Finset`, and prove both support restriction and
  zero-extension lemmas. Then use `Finset.strongInductionOn` on the active
  constraint set, since the progress lemma determines which constraint is
  erased. This avoids changing coordinate types and keeps extremality
  transport elementary.
- Model the Section 5 auxiliary object as an edge-indexed multigraph before
  formalizing contraction or split-off. `SimpleGraph` collapses parallel
  edges, while Theorems 5.12--5.14 rely on their multiplicity. Ordinary
  cut-edge connectivity under contraction is only substrate: Hind--Oellermann
  preserves terminal *element-connectivity*, which also permits deleting
  nonterminal vertices and needs a separate theorem.
- For terminal element-Menger, use a capacity-expanded incidence graph: one
  node per named edge, one per nonterminal, and `k` copies of every terminal.
  The terminal copies make undeletable terminals compatible with ordinary
  vertex Menger, while named edge nodes preserve parallel multiplicity. Prove
  both translations: element cuts block expanded paths, and every expanded
  separator below `k` yields an element cut of no larger order.
- In the Hind--Oellermann double-hit step, erase the deleted edge node from
  the tight `k`-element deletion blocker. One of the `k` disjoint paths then
  avoids the remaining `k - 1` nodes and must traverse that edge node. Since
  it is an internal degree-two incidence node, the path contains both
  nonterminal endpoints, forcing any size-`k` contraction blocker to miss a
  different packed path.
- If an agent remains on a foundational compile failure without growing a
  checked interface, stop it and split by proof boundary. Here the effective
  split was: compiling incidence encoding and cut-to-separator translation;
  separator-to-cut/Menger production; and the degree-two path lemma. Require
  each subtask to own a separate module and report a compiling declaration.
- Preserve original-host path provenance in every contraction and split-off
  state. Endpoint projection and cut-cardinality lemmas alone cannot construct
  the path attached to each final skeleton edge. Also audit split-off at two
  parallel edges with the same other endpoint: a loopless representation that
  requires distinct other endpoints is stricter than Mader's multigraph
  statement and needs an explicit reduction.
- `SimpleGraph.edgeFinset` is parameterized by a `Fintype G.edgeSet` instance.
  When a finite edge naming appears in a theorem interface, make that instance
  explicit. Otherwise independently elaborated uses can select different
  enumerations, so equal-looking edge names fail to typecheck. The
  `HostEdgeIndex` bridge is the reusable pattern: name edges by
  `Fin G.edgeFinset.card` under one explicit instance and retain an injective
  map back to `Sym2 V`.
- For Mader's dangerous-cover proof, retain minimum *cardinality*, not merely
  inclusion-minimality. Replacing two cover members by their union is justified
  only against a global cardinal-minimum property; inclusion-minimality does
  not compare the replacement family with the original one.
- In the irreducible Mader case, do not assert `X intersect Y = {t}` for every
  pair of selected dangerous sets. That equality follows only inside the
  union/intersection branch of surplus uncrossing and is used there to derive
  the difference alternative. The unconditional conclusion is that the two
  ordered differences are singleton private petals and the correction-edge
  finset has cardinality one.
- For repeated split-off, transport a finset of distinguished named copies
  through the old-edge injection. Its cardinality strictly decreases whenever
  the selected pair hits it. This gives the finite pigeonhole step in the odd
  reduction without flattening dependent edge types. To lift admissibility
  backward through earlier splits, use persistence of dangerous witnesses:
  admissible earlier splits preserve requirements and never increase cut
  cardinalities.
- Mathlib's finite undirected-tree API does not directly expose rooted child
  components. For Observation 2.12, split this layer into: unique root paths
  and parents; strict root-distance decrease and parent-chain termination;
  descendant/child-subtree connectivity and edge separation; parent-closed
  residual connectivity; then the lowest-heavy-vertex pruning arithmetic.
  Do not mix this graph layer into the already generic finite descent.
- Chuzhoy--Tan Theorem 4.20 cites the wrong number. The matching result is
  preprint Theorem 2.11 or journal Theorem 2.14.
- Chuzhoy--Tan Lemma 3.3 is under-specified as printed. Its proof needs a
  crossbar in every matching-round cluster after the odd-cluster stitching
  step; do not formalize the printed standalone implication.
- Chuzhoy Theorem 6.3 should be specialized to maximum degree three and the
  exact `AppendixA3ClusterSplitInput` consumer. A general algorithmic theorem
  adds substantial irrelevant work.
- In Chuzhoy Section 7, the paper's `rho = kappa/64` pruning budget overlooks
  the factor `d` between boundary vertices and outgoing edges. For `d = 3`, a
  smaller universal choice such as `rho = kappa/256` repairs the invariant.
- Chuzhoy Section 7 has several notation slips: Observation 7.6's cut belongs
  to the input set, Claim 7.9 needs `A intersect T`, and Observation 7.12's
  first `B` subset belongs to the first terminal set. Record corrected forms in
  theorem comments.
- Chuzhoy Observation 7.6 prints the inherited bandwidth as
  `alpha / (2 - alpha)`, but the cited Lemma 2.11 proves
  `alpha / (2 + alpha)`. The latter still weakens to `alpha / 3` and is the
  source-faithful formal target. The source sequence is
  `alpha_i = 1 / 3^(i+2)`; PDF text extraction can make the exponent look like
  multiplication.
- Chuzhoy Observation 7.7's last-half-crossing inference is false as printed.
  A lower bound on `|Gamma'(A)|` does not lower-bound
  `|A intersect Gamma'(S)|`, because `Gamma'(A)` includes new cut endpoints.
  Keep the original set `Omega = Gamma'(S)` fixed and track
  `|U intersect Omega|`; the first crossing from above `3|Omega|/4` to at most
  that threshold gives a genuine quarter-balanced cut using the same `1/8`
  edge budget. Do not use current augmented-boundary mass as a proxy for
  original terminal mass.
- The same Observation 7.7 proof also silently asserts that the terminal
  pruning set is a proper subset. This fails when the starting set is already
  `1/9`-well-linked, in particular at the minimum initial set `S0`; the inner
  loop then takes zero steps. Do not invoke minimum initiality until a genuine
  strict subset witness has been produced. Treat this as a separate source
  obligation from the corrected three-quarter crossing.
- The existing `BalancedSeparation` API minimizes overlap in a vertex
  separation. Lemma 2.11 needs a disjoint edge cut minimizing
  `edgeBoundary G A (S \ A)`, so give it a separate one-sided cut structure.
  Encode quarter-balance as `Gamma.card <= 4 * side.card`, and require an
  explicit candidate because a quarter-balanced cut need not exist when
  `Gamma.card = 1`.
- The current local-routing assembly has a real `(16*h+10)` versus
  `(16*h+12)` width discrepancy. Stop and repair the structural constants
  before trying `omega` or broadening the input silently.
- The two-gap row-stitching construction belongs to Chekuri--Chuzhoy Appendix
  C, not Claim 2.2 of that paper. Claim 2.2 is the rooted-tree leaf/path claim;
  do not perpetuate that citation when strengthening the stitching API.
- Chuzhoy--Tan Sections 4.2--4.6 consume pseudo-grid depth `64*g^4`. Running
  Theorem 4.1 at depth one leaves an assembly obligation unsupported by the
  paper, even though all types elaborate.
- Runtime, probability of success, and the sparsifier's `O(k^4)` vertex bound
  are not needed for the existential degree-three sparsifier used here.
- When an induced-cluster capacity construction is consumed by an ambient
  routing API, keep the three transports separate: project the capacity
  packing to the induced graph, use `GraphPath.mapLe` for the ambient graph,
  then reindex the finite path type with `Fintype.equivFinOfCardEq`. Prove
  congestion preservation for `mapLe` and reindexing once; unfolding all three
  transports in every downstream theorem makes endpoint and cardinality goals
  unnecessarily brittle.
- In Chekuri--Chuzhoy Claim 5.14, the width-sized flow terminals are not the
  full selected routers. Each leaf chain ends at a selected boundary subset,
  while Claim 5.15 prunes the union of the full leaf routers. Keep
  `terminal` and `router` as separate families and carry
  `terminal i ⊆ router i`; conflating them creates a false cardinality premise.
- The root boundary in Claim 5.14 also varies with the selected leaf. The paper
  independently thins every support-tree path, so require
  `rootTerminal i ⊆ rootRouter`, not one common width-sized root set. Widen only
  the target certificate after reversing each chain.
- A recursive routing-chain source must remain the boundary chosen on the
  first support edge. Do not reset it to the incoming boundary at each snoc
  step. Retain the incoming selected bundle separately because only its
  current-router endpoints are needed for the next turn.
- For global families of root-to-leaf paths, record the exact budget
  `1 + steps * (routerDen + 1)` locally and then weaken it monotonically to one
  common bound. Requiring all paths to have the same length is an avoidable and
  source-inaccurate restriction.
- To prove that a canonical root-to-leaf path avoids every selected leaf
  internally, use degree rather than tree-specific path uniqueness: each
  strict internal path vertex has two distinct path neighbors and therefore
  cannot have degree one. Pairwise cluster disjointness then upgrades vertex
  inequality to disjointness from the union of all selected leaf routers.
- The sequential internal-router composition proved here charges
  `routerDen` once per internal router, while the paper obtains the sharper
  bound from disjoint router interiors. This can add one fixed polylogarithmic
  exponent but does not change the polynomial exponent ten. Do not claim the
  paper's sharp congestion constant from this coarser chain.
- Exact endpoint thinning is easiest to obtain by applying the reserve-aware
  thinning theorem with empty reserves and then taking a subset of the
  requested cardinality. Preserve injectivity by restriction instead of
  rebuilding the matching proof.
- Claim 5.15's directed auxiliary network makes the root router a sink, but a
  host-restored path does not expose that invariant in its type. Before using
  root-internal linkages, widen the right terminal carrier to the whole root
  and apply `PathPacking.cleanToRight`. The first-hit prefix is internally
  disjoint from the root, retains the source and path count, and its target is
  an interface vertex. This avoids re-proving the directed-network semantics
  during every concatenation.
- For the final Phase 1 splice, convert each cleaned packing with
  `toPerfectUsedTerminals`, copy the exact terminal equalities, and use
  `restrictTargetSet` on the extracted root block. Compose the root linkage
  with the reversed destination leg first, then attach the source leg using
  the union of the root and destination-leg vertex set as the separating
  region. The `PerfectPathPacking` region-separated concatenation theorems
  preserve perfectness, cardinality, and directness without manual walk
  surgery.
- Keep declarations with identical semantic content under one namespace and one
  name. If a theorem already exists in the imported module (for example
  endpoint-membership of path vertices), avoid restating it with a local private
  name; that pattern can silently shadow intended lemmas and create duplicated
  goals with brittle casts.
- In the Section 5 many-leaves branch, do not select a global one-per-history-
  group transversal before forming the root-to-leaf flows. Endpoint matching
  only loses `4 * Delta`; all unsampled paths have edge congestion bounded by
  the group size. Paying the transversal factor there introduces an erroneous
  extra factor `n` and misses the source `m^19` ordinary-width exponent.
- A shared skeleton host edge away from every router forces its abstract edges
  into one history group: extend two alleged distinct-group edges to a full
  transversal and use one-per-group internal disjointness. Edges incident with
  routers are handled separately by `EndpointCongestionAtMost`.
- Preserve the negative branch of a finite-tree long-path dichotomy. It gives
  a uniform distance bound for every selected root-to-leaf path; discarding it
  and using `Fintype.card` can introduce a full factor `n`.
- Generic routing concatenation adds congestion budgets and is too coarse for
  the source exponent when successive internal-router zones are disjoint and
  all support segments share one global history-group load bound. Carry those
  two edge-zone invariants through the chain and take their sum once, rather
  than once per meta-edge.
- If exponent 24 is accepted for WP1C, the generic congestion sum is sufficient:
  the concrete monomial is `W * m^24 * Delta^10 * log_2(x)^5`. Keep this as a
  named endpoint and propagate it explicitly as the `ell^50` A.2 route.
- In the Theorem 4.6 many-leaves recursion, keep the selected-leaf count as the
  structural length invariant. At a binary node, reserve disjoint connector
  blocks before recursing, join the two child systems, and prove first/last
  indices through dedicated `castLength` lemmas; broad `simp` over dependent
  `Fin` casts is brittle.
- For journal Theorem 5.11, follow the numbered PARTITION and SEPARATE actions
  rather than importing the overview's CNS deletion shortcut. Normalize an
  acceptable clustering by finite minimal refinement until every large block
  has bandwidth; edge-Menger then gives either the router or the SEPARATE cut,
  and the rational source potential supplies the outer finite descent.
- The bandwidth cap produced by that source-faithful loop is `w0 / 2`, not the
  unrelated global size parameter used in the logarithmic denominator. Carry
  this cap through the Phase 1 and Phase 2 consumers and discharge their width
  requirements from the skeleton-flow budget.

## Verification commands

```bash
lake build +«statements-and-proofs».ChangedModule
lake env lean AxiomAudit.lean
lake build
```

Before reporting a closed package, also scan the relevant closure for
`sorry`, `admit`, new project axioms, and accidental use of a contract theorem.

- `native_decide` introduces a generated axiom into `#print axioms`, even for
  a tiny finite computation.  For trust-sensitive endpoints use kernel
  reduction (`decide`, `norm_num`, or an explicit finite proof) and audit the
  final theorem rather than assuming a successful compile is sufficient.
