# Exponent-eight source and Lean map

Last audited: 2026-07-29

This document maps the Chuzhoy--Tan Section 4 and Section 5 objects needed by
the experimental recursive-slicing route.  It is deliberately separate from
the completed exponent-ten endpoint.  Nothing listed here changes
`polynomialGridMinorTreewidthBound10` or a public polynomial-grid-minor
theorem.

Line numbers refer to the worktree based on commit `5263735`, together with the
new files under `statements-and-proofs/Exponent8/`.

## Source-numbering warning

The result referred to as "Theorem 4.5" in the work request is **Lemma 4.5** in
Chuzhoy--Tan, *Towards Tight(er) Bounds for the Excluded Grid Theorem*,
`grid-minor-theorem.pdf`.  The repository follows the source and calls it
Lemma 4.5.

Chuzhoy--Tan Claim 5.3 and Observation 5.4 are not currently formalized.
Declarations in files named `ChekuriChuzhoySection5...` concern a different
paper and must not be used as implementations of these two Chuzhoy--Tan
statements.

## Dependency overview

The principal existing dependency chain is:

```text
Paths
  +--> Crossbar
  +--> PseudoGrid --> PseudoGridSlicingDefs
                           |
                           v
                 PseudoGridSlicing --> Observation44Reduction
                           |                    |
                           v                    v
                 UniqueLinkageOrdering      Section42ActualPaths
                           |
                           v
                       Theorem46
                           |
                           v
                       Section43 --> Section44 --> Section45
                           |                         |
                           |                         v
                           |                 Section45PseudoGrid
                           |
                           +--> Exponent8/Lemma48Additive --------+
                           |                                     |
                           +--> Exponent8/LastHitSelection        |
                                      |                          |
Crossbar + Section43 ---------------->+                          |
                                      v                          |
                           Exponent8/LastHitCrossbar              |
                                      |                          |
                                      v                          |
                            Exponent8/Claim53Strong               |
                                      |                          |
                                      +----------+---------------+
                                                 v
                                  Exponent8/RecursiveSlicing
```

The new additive Lemma 4.8 module imports only `Section43`.  It does not import
the polynomial-grid-minor endpoint and is not currently part of its aggregate
import.

## 1. Slicing and slice localization

### 1.1 Slicing object

Declaration:

```lean
SimpleGraph.PathSlicing
```

Location: `statements-and-proofs/PseudoGridSlicingDefs.lean:58`

Signature:

```lean
structure PathSlicing
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V}
    (R : PerfectPathPacking G A B) (M : Nat) where
  cut : R.Index -> Fin (M + 1) -> V
  cut_mem : forall r t, cut r t ∈ (R.path r).vertexSet
  cut_zero : forall r, cut r 0 = (R.path r).source
  cut_last : forall r, cut r (Fin.last M) = (R.path r).target
  cut_monotone :
    forall r {s t : Fin (M + 1)}, s <= t ->
      (R.path r).Before (cut r s) (cut r t)
```

Direct dependency: `PerfectPathPacking` and `GraphPath.Before`, both from
`Paths.lean`, through `PseudoGrid.lean`.

### 1.2 Strict slice and path-localization invariant

Declarations:

```lean
SimpleGraph.PathSlicing.SliceInterior
SimpleGraph.PathSlicing.PathInSlice
SimpleGraph.PathSlicing.pathsInSlice
SimpleGraph.PathSlicing.WidthAtLeast
```

Locations:

- `PseudoGridSlicingDefs.lean:274`
- `PseudoGridSlicingDefs.lean:284`
- `PseudoGridSlicingDefs.lean:293`
- `PseudoGridSlicingDefs.lean:307`

Signatures:

```lean
def SliceInterior
    (sigma : PathSlicing R M) (r : R.Index)
    (i : Fin M) (v : V) : Prop

def PathInSlice
    (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T)
    (i : Fin M) (q : Qpack.Index) : Prop :=
  forall {r : R.Index} {v : V},
    v ∈ (Qpack.path q).vertexSet ->
    v ∈ (R.path r).vertexSet ->
    sigma.SliceInterior r i v

noncomputable def pathsInSlice
    (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T)
    (i : Fin M) : Finset Qpack.Index

def WidthAtLeast
    (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T)
    (w : Nat) : Prop :=
  forall i : Fin M, w <= (sigma.pathsInSlice Qpack i).card
```

`PathInSlice` says that **every intersection of the selected `Q`-path with a
row lies in the strict `i`th row interval**.  It does not say that the entire
`Q`-path lies in the union of the row intervals.  A new theorem requiring
whole-path containment must therefore state that additional invariant rather
than silently reading it from `PathInSlice`.

Useful direct consequences:

```lean
SimpleGraph.PathSlicing.pathsInSlice_disjoint
```

at `Section43.lean:774`, and

```lean
SimpleGraph.PathSlicing.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
```

at `Section43.lean:760`.

### 1.3 Generic slicing theorem: Chuzhoy--Tan Theorem 4.6

Declaration:

```lean
SimpleGraph.PathSlicing.theorem46
```

Location: `statements-and-proofs/Theorem46.lean:24`

Signature:

```lean
theorem theorem46
    (R : PerfectPathPacking G A B)
    (Qpack : PathPacking G S T)
    (M w : Nat)
    (hM : 0 < M) (hw : 0 < w)
    (hunique : R.IsUniqueLinkage)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hcard : M * w + (M + 1) * R.card <= Qpack.card) :
    ∃ sigma : PathSlicing R M, sigma.WidthAtLeast Qpack w
```

Direct dependencies:

- `SimpleGraph.PathSlicing.exists_slicing_of_linkageOrdering`,
  `PseudoGridSlicing.lean:1528`;
- `SimpleGraph.PathSlicing.linkageOrderingOfUnique`,
  `UniqueLinkageOrdering.lean:2501`.

Transitive mathematical dependency: Chuzhoy--Tan Lemma 4.5, followed by the
threshold-counting proof of Theorem 4.6.

### 1.4 Source-faithful pseudo-grid slicing with actual auxiliary paths

Declaration:

```lean
SimpleGraph.PseudoGrid.section42_slicing_minor_of_pseudoGrid_actualPaths
```

Location: `statements-and-proofs/Section42ActualPaths.lean:27`

Near-exact signature:

```lean
theorem section42_slicing_minor_of_pseudoGrid_actualPaths
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card <=
        Gamma.goodQSet.card) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (A' B' S T : Finset W)
      (R : PerfectPathPacking H A' B')
      (Qpack : PathPacking H S T)
      (sigma : PathSlicing R M),
        IsMinor H G ∧
        MaxDegreeAtMost H 4 ∧
        R.IsUniqueLinkage ∧
        R.card = Gamma.rowPacking.card ∧
        Qpack.card = Gamma.goodQSet.card ∧
        (forall q : Qpack.Index,
          D <=
            ((Finset.univ : Finset R.Index).filter fun r =>
              ¬ Disjoint (Qpack.path q).vertexSet
                (R.path r).vertexSet).card) ∧
        sigma.WidthAtLeast Qpack w
```

Direct dependencies:

- `Section4Reduction.PseudoGrid.exists_observation44_reduced_state`,
  `Observation44Reduction.lean:1430`;
- `Observation44State.reducedGraph`, `reducedRow`, and `reducedRetained`,
  `Observation44Reduction.lean:934`, `:953`, and `:964`;
- `Observation44State.reducedRow_isUniqueLinkage`,
  `Observation44Reduction.lean:1211`;
- `Observation44State.reducedRetained_card`,
  `reducedRetained_metRows_card`, and
  `reducedRetained_intersects_reducedRow`,
  `Observation44Reduction.lean:977`, `:986`, and `:1027`;
- `PathSlicing.theorem46`.

This is the slicing entry point to use when later arguments need actual
auxiliary paths.  The older contact-path shortcut replaces each auxiliary path
by a reflexive path and loses the geometry required by a last-hit proof.

### 1.5 One-slice cleanup and retained localization

Declaration:

```lean
SimpleGraph.PathSlicing.SliceIntersectingSubfamilies
```

Location: `statements-and-proofs/Section43.lean:904`

Relevant fields:

```lean
structure SliceIntersectingSubfamilies
    (sigma : PathSlicing R M)
    (Qpack : PathPacking G S T)
    (i : Fin M) (w D : Nat) where
  rows : Finset R.Index
  paths : Finset Qpack.Index
  rows_subset : rows ⊆ Finset.univ
  paths_subset : paths ⊆ sigma.pathsInSlice Qpack i
  intersecting :
    sigma.SliceIntersectingPathSetPair Qpack i rows paths w D
  half_paths :
    (sigma.pathsInSlice Qpack i).card <= 2 * paths.card
  discarded_rows_sparse :
    forall r ∈ (Finset.univ : Finset R.Index) \ rows,
      (sigma.segmentIntersectingRightIndices
        Qpack i paths r).card <= w
```

Producer:

```lean
SimpleGraph.PathSlicing.exists_slice_intersecting_subfamilies
```

at `Section43.lean:929`.

The structure should eventually receive a slice-level additive-loss field
derived from the new additive Lemma 4.8 theorem.  At present the additive
module exposes the packing-level result but deliberately does not modify this
existing structure.

### 1.6 Per-slice support and happy-core localization

Declarations:

```lean
SimpleGraph.PathSlicing.sliceSupportVertexSet
SimpleGraph.PathSlicing.cleanedSupportVertexSet
SimpleGraph.PathSlicing.cleanedSupportGraph_support_subset_sliceSupport
SimpleGraph.PathSlicing.SlicedHappyCores
SimpleGraph.PathSlicing.exists_slicedHappyCores
```

Locations:

- `Section45PseudoGrid.lean:188`
- `Section45PseudoGrid.lean:195`
- `Section45PseudoGrid.lean:212`
- `Section45PseudoGrid.lean:1079`
- `Section45PseudoGrid.lean:1090`

`exists_slicedHappyCores` depends directly on
`exists_slice_intersecting_subfamilies` and
`Section44.PathPacking.theorem411`, then packages a cleaned family and one
connected happy core for each slice.

## 2. Chuzhoy--Tan Lemma 4.5

### 2.1 Output structure

Declaration:

```lean
SimpleGraph.PathSlicing.LinkageOrdering
```

Location: `statements-and-proofs/PseudoGridSlicingDefs.lean:95`

The structure records:

- an injective rank below `Fintype.card V`;
- strict rank increase along every oriented row;
- one selected separator vertex per row and threshold;
- monotonicity of the selected row vertices;
- the exact separator set;
- the one-step separator update invariant;
- separator cardinality at most `R.card`;
- blocking of every path that crosses a rank threshold.

### 2.2 Main producer

Declaration:

```lean
SimpleGraph.PathSlicing.linkageOrderingOfUnique
```

Location: `statements-and-proofs/UniqueLinkageOrdering.lean:2501`

Signature:

```lean
noncomputable def linkageOrderingOfUnique
    {R : PerfectPathPacking G A B}
    (hunique : R.IsUniqueLinkage) :
    LinkageOrdering R
```

Direct dependencies:

- `SimpleGraph.PathSlicing.linkageDependency_acyclic_of_unique`,
  `UniqueLinkageOrdering.lean:1818`;
- `TopologicalRank.linkageOrderingOfUniqueOfDependencyAcyclic`,
  `UniqueLinkageOrdering.lean:2489`;
- `topologicalRankOfAcyclicRelation`,
  `UniqueLinkageOrdering.lean:622`.

The acyclicity theorem contains the Appendix B rerouting contradiction.  The
topological rank is then converted to the exact separator object used by
Theorem 4.6.

## 3. Chuzhoy--Tan Lemma 4.8

### 3.1 Existing half-retention theorem

Declaration:

```lean
SimpleGraph.PathPacking.exists_intersecting_path_subfamilies
```

Location: `statements-and-proofs/Section43.lean:657`

Signature:

```lean
theorem exists_intersecting_path_subfamilies
    (R : PathPacking G S T)
    (Q : PathPacking G S' T')
    (Rset : Finset R.Index)
    (Qset : Finset Q.Index)
    {w D : Nat}
    (hD : 0 < D)
    (hdense :
      forall q ∈ Qset,
        2 * D <=
          (R.intersectingLeftIndices Q Rset q).card)
    (hcard : 2 * Rset.card * w <= D * Qset.card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
      Q' ⊆ Qset ∧
      IntersectingPathSetPair R Q R' Q' w D ∧
      Qset.card <= 2 * Q'.card ∧
      forall r ∈ Rset \ R',
        (R.intersectingRightIndices Q Q' r).card <= w
```

Direct dependency:

```lean
SimpleGraph.FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets
```

at `Section43.lean:533`.

### 3.2 Existing charge inequality inside the old proof

Declaration:

```lean
SimpleGraph.FiniteBipartitePruning.PruneTrace
  .deleted_right_mul_le_deleted_left_mul
```

Location: `statements-and-proofs/Section43.lean:514`

Signature:

```lean
theorem deleted_right_mul_le_deleted_left_mul
    (h : PruneTrace (rel := rel) (w := w) (D := D)
      A B Afinal Bfinal)
    (P : Finset alpha)
    (hdisj : Disjoint P A)
    (hPbad :
      forall a ∈ P, (B.bipartiteAbove rel a).card < w)
    (hdense :
      forall b ∈ B,
        2 * D <= ((P ∪ A).bipartiteBelow rel b).card) :
    (B \ Bfinal).card * D <=
      (P ∪ (A \ Afinal)).card * w
```

The old proof calls this theorem with `P = empty`, obtaining

```lean
(B \ Bfinal).card * D <= (A \ Afinal).card * w.
```

The weaker half-retention theorem previously discarded this exact inequality
after using it in arithmetic.

### 3.3 New additive strengthening

Module:

```text
statements-and-proofs/Exponent8/Lemma48Additive.lean
```

This module imports `Section43` and reuses
`deleted_right_mul_le_deleted_left_mul`.  It does not repeat the pruning
argument.

Generic core declaration:

```lean
SimpleGraph.FiniteBipartitePruning.PruneTrace
  .exists_intersecting_subsets_additive_core
```

Location: `Exponent8/Lemma48Additive.lean:50`

Core conclusion:

```lean
(B \ Bfinal).card * Dhat <=
  (A \ Afinal).card * wHat
```

It needs the density hypothesis but neither `0 < Dhat` nor the global
half-retention cardinality hypothesis.

Generic literal strengthening:

```lean
SimpleGraph.FiniteBipartitePruning.PruneTrace
  .exists_intersecting_subsets_additive
```

Location: `Exponent8/Lemma48Additive.lean:97`

This adds the original half-retention conclusion to the exact loss.

Path-packing core declaration:

```lean
SimpleGraph.PathPacking
  .exists_intersecting_path_subfamilies_additive_core
```

Location: `Exponent8/Lemma48Additive.lean:160`

Signature:

```lean
theorem exists_intersecting_path_subfamilies_additive_core
    (R : PathPacking G S T)
    (Q : PathPacking G S' T')
    (Rset : Finset R.Index)
    (Qset : Finset Q.Index)
    {wHat Dhat : Nat}
    (hdense :
      forall q ∈ Qset,
        2 * Dhat <=
          (R.intersectingLeftIndices Q Rset q).card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
      Q' ⊆ Qset ∧
      IntersectingPathSetPair R Q R' Q' wHat Dhat ∧
      (Qset \ Q').card * Dhat <=
        (Rset \ R').card * wHat ∧
      forall r ∈ Rset \ R',
        (R.intersectingRightIndices Q Q' r).card <= wHat
```

Literal path-packing strengthening:

```lean
SimpleGraph.PathPacking
  .exists_intersecting_path_subfamilies_additive
```

Location: `Exponent8/Lemma48Additive.lean:198`

This has the original Lemma 4.8 hypotheses and conclusions and additionally
returns

```lean
(Qset \ Q').card * Dhat <=
  (Rset \ R').card * wHat.
```

Coarse requested corollary:

```lean
SimpleGraph.PathPacking
  .exists_intersecting_path_subfamilies_additive_coarse
```

Location: `Exponent8/Lemma48Additive.lean:241`

It returns the division-free inequality

```lean
(Qset \ Q').card * Dhat <= Rset.card * wHat.
```

Direct dependencies of all three path-packing declarations:

- the corresponding generic additive theorem in the same module;
- `PathPacking.PathsIntersect`,
  `intersectingLeftIndices`, and `intersectingRightIndices` from
  `Section43.lean`;
- transitively, the original charge inequality at `Section43.lean:514`.

## 4. Chuzhoy--Tan Theorem 4.11

### 4.1 Output

Declaration:

```lean
SimpleGraph.Section44.PathPacking.Theorem411Output
```

Location: `statements-and-proofs/Section44.lean:3012`

Near-exact shape:

```lean
structure Theorem411Output
    (P : PathPacking G S T)
    (I : Finset P.Index)
    (w D : Nat) where
  ClusterIndex : Type u
  [clusterFintype : Fintype ClusterIndex]
  [clusterDecidableEq : DecidableEq ClusterIndex]
  cluster : ClusterIndex -> Finset V
  cluster_disjoint :
    Pairwise fun c d => Disjoint (cluster c) (cluster d)
  happy : forall c, HappyCluster P I (cluster c) w D
  retained : Finset P.Index
  retained_subset : retained ⊆ I
  quarter_retained : I.card <= 4 * retained.card
  retained_contained :
    forall i ∈ retained, ∃ c,
      i ∈ containedInCluster P I (cluster c)
```

### 4.2 Main theorem

Declarations:

```lean
SimpleGraph.Section44.PathPacking.Theorem411Statement
SimpleGraph.Section44.PathPacking.theorem411
```

Locations:

- `Section44.lean:3351`
- `Section44.lean:3365`

Signature of the proposition:

```lean
def Theorem411Statement : Prop :=
  forall {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S T S' T' : Finset V}
    (Sigma : PathPacking G S T)
    (Q : PathPacking G S' T')
    (I : Finset Sigma.Index)
    (J : Finset Q.Index)
    {w D : Nat},
      0 < w ->
      0 < D ->
      Sigma.IntersectingPathSetPair Q I J
        (4 * w) (2 * D) ->
      8 * w <= D ->
      Nonempty (Theorem411Output Sigma I w D)

theorem theorem411 : Theorem411Statement
```

Direct proof dependencies:

- `theorem411_of_splitter`, `Section44.lean:3321`;
- `DecompositionState.exists_sparse_cut_of_not_good`,
  `Section44.lean:2185`;
- `DecompositionState.childSurvivors_of_sparse_cut`,
  `Section44.lean:2167`;
- `DecompositionState.exists_final_state_of_splitter`,
  `Section44.lean:2557`;
- `Theorem411Output.ofFinalDecompositionState_of_pos`,
  `Section44.lean:3241`.

Transitive dependencies include `EdgeMenger.lean` for the sparse-cut theorem
and `Section43.lean` for intersecting path families.

## 5. Chuzhoy--Tan Theorem 4.15

### 5.1 Large-overlap relation

Declaration:

```lean
SimpleGraph.Section45.LargeOverlapRel
```

Location: `statements-and-proofs/Section45.lean:176`

Signature:

```lean
def LargeOverlapRel
    {N M : Nat}
    (S : Fin M -> Finset (Fin N))
    (w : Nat)
    (i j : Fin M) : Prop :=
  i < j ∧ w <= (S i ∩ S j).card
```

### 5.2 Main theorem

Declaration:

```lean
SimpleGraph.Section45.theorem415
```

Location: `statements-and-proofs/Section45.lean:437`

Signature:

```lean
theorem theorem415
    {N M D w : Nat}
    (S : Fin M -> Finset (Fin N))
    (hN : 3 * w <= N)
    (hDsq : 4 * N * w <= D ^ 2)
    (hlarge : 2 * N * w <= D * M)
    (hcard : forall i : Fin M, D <= (S i).card) :
    ∃ l : List (Fin M),
      l.length = w ∧
      l.IsChain (LargeOverlapRel S w)
```

Direct proof dependencies:

- `sum_rowDegrees_eq_sum_card`, `Section45.lean:181`;
- `sum_rowDegrees_sq_eq_sum_intersections`, `Section45.lean:212`;
- `independent_bound_of_theorem415_hypotheses`,
  `Section45.lean:338`;
- `theorem415_from_independent_bound`, `Section45.lean:408`;
- `exists_relChainIn_of_weighted_independent_bound`,
  `Section45.lean:104`.

The graph-realization layer after this numerical theorem begins with
`Section45Input` at `Section45.lean:1068` and culminates in
`section45_weak_pathOfSetsSystem` at `Section45.lean:1185`.

## 6. Chuzhoy--Tan Claim 5.3

Status: the original `O(g^6)` conclusion has been superseded in the
experimental folder by an axiom-free `O(g^4)` strengthening.

Do not confuse this result with:

```lean
SimpleGraph.ChekuriChuzhoySection5TerminalEdgeCount
  .terminal_card_le_three_mul_nonterminalEdges
```

at `ChekuriChuzhoySection5TerminalEdgeCount.lean:525`.  That declaration is
preprint Claim 5.1 / journal Claim 5.3 of the Chekuri--Chuzhoy paper and is
mathematically unrelated to the Chuzhoy--Tan type-2 slicing claim.

### 6.1 Slice localization and uncontracting

Declaration:

```lean
SimpleGraph.Exponent8.SliceLocalizationInvariant
```

Location: `statements-and-proofs/Exponent8/LastHitCrossbar.lean:32`

This structure connects one contracted slice to its original graph.  Its
signature is parameterized by original perfect packings

```lean
P : PerfectPathPacking G A B
Q : PerfectPathPacking G A X
```

and contracted representatives

```lean
Rbar : PerfectPathPacking H Abar Bbar
Qbar : PathPacking H Sbar Tbar
sigma : PathSlicing Rbar M
i : Fin M.
```

The exact provenance fields are:

```lean
rowRoot : Rbar.Index -> P.Index
rowRoot_injective : Function.Injective rowRoot
uncontractedSegment : Rbar.Index -> GraphPath G
segment_vertexSet_subset_main : ...
uncontractedQ : Qbar.Index -> GraphPath G
qParent : Qbar.Index -> Q.Index
qParent_injective : Function.Injective qParent
uncontractedQ_vertexSet_subset_parent : ...
uncontractedQ_edgeSet_subset_parent : ...
localizedQ : Finset Qbar.Index
localizedQ_subset_slice :
  localizedQ ⊆ sigma.pathsInSlice Qbar i
uncontractedQ_exactlyOneEndpointIn_X : ...
contracted_hit_iff_uncontracted_hit : ...
main_hit_localized : ...
X_disjoint_main : ...
```

In particular, pairwise disjointness of the uncontracted auxiliary paths is
not an input field.  It is proved at `LastHitCrossbar.lean:179` from
`qParent_injective`, path containment, and the node-disjointness of `Q`.

The rooted Observation 4.4 producer now constructs this structure for every
chosen slice and every subfamily of `pathsInSlice`; see Section 10.3 below.

### 6.2 Last-hit crossbar

Declarations:

```lean
SimpleGraph.Exponent8.SliceLocalizationInvariant.LastHitCrossbar
SimpleGraph.Exponent8.SliceLocalizationInvariant.lastHitCrossbar_direct
SimpleGraph.Exponent8.SliceLocalizationInvariant.lastHitCrossbar
```

Locations:

- `Exponent8/LastHitCrossbar.lean:633`
- `Exponent8/LastHitCrossbar.lean:534`
- `Exponent8/LastHitCrossbar.lean:656`

The direct theorem has signature:

```lean
theorem lastHitCrossbar_direct
    (L : SliceLocalizationInvariant
      G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index)
    (Qset : Finset Qbar.Index)
    (d r : Nat)
    (hd : 0 < d)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap :
      forall b ∈ bad, (L.hitQAt Qset b).card <= d)
    (hmany :
      d * r <= (L.badHitQ bad Qset).card) :
    Nonempty (Crossbar G A B X r)
```

`lastHitCrossbar` packages this as the proposition `LastHitCrossbar`.
The proof explicitly:

1. orients every uncontracted auxiliary path toward `X`;
2. takes its last hit of the union of bad uncontracted row segments;
3. proves the owner row exists and is unique using main-path disjointness;
4. applies the bounded-fiber selection theorem from
   `Exponent8/LastHitSelection.lean`;
5. truncates each chosen path with `cleanSuffixFromSet`;
6. proves all main/spoke disjointness and exit fields of `Crossbar`.

The finite counting dependency is:

```lean
SimpleGraph.Exponent8.exists_lastHitSelection
```

at `Exponent8/LastHitSelection.lean:86`.

### 6.3 Strengthened Claim 5.3

Module:

```text
statements-and-proofs/Exponent8/Claim53Strong.lean
```

Declarations:

```lean
SimpleGraph.Exponent8.SliceLocalizationInvariant
  .badHitQ_card_lt_of_no_crossbar
SimpleGraph.Exponent8.SliceLocalizationInvariant.claim53Strong
SimpleGraph.Exponent8.SliceLocalizationInvariant
  .badHitQ_card_lt_four_mul_g_pow_four
SimpleGraph.Exponent8.SliceLocalizationInvariant
  .claim53Strong_four_mul_g_pow_four
```

Locations: `Claim53Strong.lean:66`, `:83`, `:108`, and `:127`.

The generic exact loss theorem is:

```lean
theorem badHitQ_card_lt_of_no_crossbar
    ...
    (hd : 0 < d)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap :
      forall b ∈ bad, (L.hitQAt Qset b).card <= d)
    (hnoCrossbar :
      not Nonempty (Crossbar G A B X r)) :
    (L.badHitQ bad Qset).card < d * r
```

Writing

```lean
L.goodQ bad Qset = Qset \ L.badHitQ bad Qset,
```

`claim53Strong` returns the compositional division-free form:

```lean
Qset.card <= (L.goodQ bad Qset).card + d * r.
```

For the paper's local incidence cap `d = 4 * g^2` and forbidden crossbar
width `r = g^2`, the two specialized declarations prove:

```lean
(L.badHitQ bad Qset).card < 4 * g^4

Qset.card <= (L.goodQ bad Qset).card + 4 * g^4.
```

Thus the recursive bookkeeping loses `O(g^4)`, rather than the printed
`O(g^6)`.

Direct dependencies of the strengthened claim are:

- the slice-localization invariant;
- `lastHitCrossbar_direct`;
- the `Crossbar` structure below;
- retained original-`Q` provenance through contractions.

The additive Lemma 4.8 result is logically independent of the last-hit claim;
the future recursive slicing bookkeeping consumes both results.  The graph
proof itself uses these existing path primitives:

```lean
SimpleGraph.GraphPath.lastHitVertex
SimpleGraph.GraphPath.lastHitVertex_spec
SimpleGraph.GraphPath.eq_lastHitVertex_of_mem_dropUntil_of_mem_set
SimpleGraph.GraphPath.cleanSuffixFromSet
SimpleGraph.GraphPath.cleanSuffixFromSet_vertexSet_subset
SimpleGraph.GraphPath.cleanSuffixFromSet_edgeSet_subset
SimpleGraph.GraphPath.cleanSuffixFromSet_inter_eq_singleton_source
SimpleGraph.GraphPath.orient_target_mem
```

at `Paths.lean:1114`, `:1118`, `:1147`, `:1163`, `:1180`, `:1186`, `:1926`,
and `:2131`.

## 7. Chuzhoy--Tan Observation 5.4

Status: **absent**.

There is currently no Lean declaration proving that the type-2 slice graph
`H_i'`, obtained after deleting auxiliary paths meeting the discarded row
segments and then deleting those separated row components, has the perfect
unique linkage property for the retained row subfamily.

Do not confuse this with the unrelated `Observation 5.4` comments in
`ChekuriChuzhoySection5SourcePotential.lean`.

The nearest existing restriction API is:

```lean
SimpleGraph.PerfectPathPacking.restrictIndexSet
```

at `Paths.lean:4629`, with cardinality and support lemmas at
`Paths.lean:4672-4718`.  No existing theorem states that
`PerfectPathPacking.IsUniqueLinkage` is inherited after deleting separated
components or restricting to the corresponding path indices.  That hereditary
unique-linkage theorem is a genuine missing dependency of Observation 5.4.

## 8. Crossbar

Declaration:

```lean
SimpleGraph.Crossbar
```

Location: `statements-and-proofs/Crossbar.lean:90`

Near-exact shape:

```lean
structure Crossbar
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V)
    (A B X : Finset V)
    (rho : Nat) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  card_index : Fintype.card Index = rho
  mainPath : Index -> GraphPath G
  main_connects :
    forall i, (mainPath i).Connects A B
  main_nodeDisjoint :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint (mainPath i) (mainPath j)
  spokePath : Index -> GraphPath G
  spoke_connects :
    forall i,
      (spokePath i).ConnectsPathToSet (mainPath i) X
  spoke_nodeDisjoint :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint (spokePath i) (spokePath j)
  spoke_meets_own_main :
    forall i, ∃ v,
      (spokePath i).IsEndpoint v ∧
      (mainPath i).MeetsExactlyAt (spokePath i) v
  spoke_exits_own_main :
    forall i, ∃ v,
      (spokePath i).IsEndpoint v ∧
      (mainPath i).MeetsExactlyAt (spokePath i) v ∧
      (spokePath i).otherEndpoint v ∈ X ∧
      (spokePath i).otherEndpoint v ∉
        (mainPath i).vertexSet
  spoke_disjoint_other_main :
    forall {i j}, i ≠ j ->
      GraphPath.NodeDisjoint (mainPath i) (spokePath j)
```

Direct dependency: `Paths.lean`.

Useful existing operations:

- `Crossbar.reindex`, `Crossbar.lean:169`;
- `Crossbar.finReindex`, `Crossbar.lean:237`;
- `Crossbar.mapLe`, `Crossbar.lean:263`.

An existing construction pattern is:

```lean
SimpleGraph.Theorem41Setup.ContractedLinkage.toCrossbar
```

at `Theorem41.lean:1408`.  It is specialized to a Theorem 4.1 contracted
linkage and width `g^2`; it is not a general implementation of
`LastHitCrossbar`.  Its use of `cleanSuffixFromSet` is nevertheless the closest
proved template for exact spoke attachment and disjointness.

## 9. Perfect unique linkage

Declarations:

```lean
SimpleGraph.PerfectPathPacking.SpansVertices
SimpleGraph.PerfectPathPacking.IsUniqueLinkage
```

Locations:

- `statements-and-proofs/PseudoGridSlicingDefs.lean:42`
- `statements-and-proofs/PseudoGridSlicingDefs.lean:48`

Signatures:

```lean
def SpansVertices
    (R : PerfectPathPacking G A B) : Prop :=
  forall v : V, v ∈ R.toPathPacking.vertexSet

def IsUniqueLinkage
    (R : PerfectPathPacking G A B) : Prop :=
  R.SpansVertices ∧
  forall R' : PerfectPathPacking G A B,
    R'.toPathPacking.edgeSet =
      R.toPathPacking.edgeSet
```

Main existing producers:

```lean
SimpleGraph.PerfectPathPacking.isUniqueLinkage_of_edge_deletion_bound
```

at `PseudoGridSlicing.lean:1910`;

```lean
SimpleGraph.PseudoGrid.rowPerfectPackingInRowSupport_isUniqueLinkage
```

at `PseudoGridSlicing.lean:3895`;

```lean
SimpleGraph.PseudoGrid.observation_four_four_unique_linkage_reduction
```

at `PseudoGridSlicing.lean:4422`; and

```lean
SimpleGraph.Section4Reduction.Observation44State
  .reducedRow_isUniqueLinkage
```

at `Observation44Reduction.lean:1211`.

The first producer reduces uniqueness to the absence of a full linkage after
deleting a row edge.  The row-support producer proves uniqueness directly in
the exact union of row paths.  The source-faithful reduction producer proves
the Observation 4.4 version after retaining actual auxiliary paths through the
contraction process.

## 10. Contracted and uncontracted auxiliary-path representation

The original pseudo-grid records genuine paths in the original graph:

```lean
PseudoGrid.qPath : QIndex -> GraphPath G
PseudoGrid.qPath_subset_matched
PseudoGrid.qPath_edgeSet_subset_matched
```

at `PseudoGrid.lean:326`, `:330`, and `:338`.

The actual retained family is packaged by:

```lean
SimpleGraph.PseudoGrid.goodQPathPacking
```

at `PseudoGridSlicing.lean:2154`, with original-`Q` edge provenance:

```lean
SimpleGraph.PseudoGrid.goodQPathPacking_edgeSet_subset_Q
```

at `PseudoGridSlicing.lean:2177`.

The source-faithful contraction state is:

```lean
SimpleGraph.Section4Reduction.Observation44State
```

at `Observation44Reduction.lean:29`.  Its relevant fields are:

```lean
originalQ : PerfectPathPacking K Aq Bq
retainedQ : PathPacking H Sq Tq
parent : retainedQ.Index -> originalQ.Index
parent_injective : Function.Injective parent
retained_vertex_subset :
  forall i,
    (retainedQ.path i).vertexSet ⊆
      (originalQ.path (parent i)).vertexSet
retained_edge_subset :
  forall i,
    (retainedQ.path i).edgeSet ⊆
      (originalQ.path (parent i)).edgeSet
```

These containment fields survive each contraction, but they do not imply that
every intersection of an initial auxiliary path with an initial row survives:
an arbitrary retained subpath could omit such an intersection.  Exact
incidence is now carried by the enriched state:

```lean
SimpleGraph.Exponent8.RootedObservation44State
```

at `statements-and-proofs/Exponent8/Observation44RootProvenance.lean:45`,
with signature:

```lean
structure RootedObservation44State
    (Gamma : PseudoGrid G A B X g D P Q) where
  state :
    Observation44State G D Gamma.rowPacking.card
      Gamma.goodQPathPacking.card
  rowRoot :
    state.row.Index ≃ Gamma.rowPerfectPackingInHPrime.Index
  qRoot :
    state.retainedQ.Index ≃ Gamma.goodQPathPackingInHPrime.Index
  hit_iff_root :
    forall r q,
      PathPacking.PathsIntersect
          (state.row.path r) (state.retainedQ.path q) ↔
        PathPacking.PathsIntersect
          (Gamma.rowPerfectPackingInHPrime.path (rowRoot r))
          (Gamma.goodQPathPackingInHPrime.path (qRoot q))
```

The two one-step preservation theorems are:

```lean
RootedObservation44State.contractCommonEdge_hit_iff
RootedObservation44State.contractOffRowEdge_hit_iff
```

at `Observation44RootProvenance.lean:91` and `:176`.  They depend on:

- the projection vertex-set equations of `RetainedProjection`;
- `EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq`;
- node-disjointness of the row and retained families; and
- for the off-row move, membership of the contracted edge in its retained
  auxiliary path.

The rooted transition constructors are at lines `:269` and `:292`.  The
rooted strict-decrease theorems are:

```lean
RootedObservation44State.exists_smaller_of_common_edge
RootedObservation44State.exists_smaller_of_off_row_vertex
```

at lines `:324` and `:385`.  They refactor the two corresponding
`Observation44State` moves but retain the fixed root maps.  Finite
minimization is therefore performed over incidence-certified enriched
states:

```lean
theorem RootedObservation44State.exists_reduced_of_pseudoGrid
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) :
    ∃ Root : RootedObservation44State Gamma,
      Root.state.IsReduced
```

at `Observation44RootProvenance.lean:477`.  Its dependencies are the initial
Observation 4.4 state, both rooted strict-decrease theorems, and
well-founded minimization of `Fintype.card Root.state.W`.

Reduced-support incidence is exported by:

```lean
RootedObservation44State.reduced_hit_iff_root_hit
```

at line `:559`.  Finally, the source-path bridge requested by
`LastHitCrossbar` is now an ordinary definition:

```lean
noncomputable def
    RootedObservation44State.toSliceLocalizationInvariant_fullRows
    (Root : RootedObservation44State Gamma)
    (hReduced : Root.state.IsReduced)
    (sigma : PathSlicing (Root.state.reducedRow hReduced) M)
    (i : Fin M)
    (localizedQ :
      Finset (Root.state.reducedRetained hReduced).Index)
    (hlocalized :
      localizedQ ⊆
        sigma.pathsInSlice (Root.state.reducedRetained hReduced) i)
    (hXdisjoint :
      forall p : P.Index, Disjoint X (P.path p).vertexSet) :
    SliceLocalizationInvariant
      G (Root.state.reducedGraph hReduced) A B X P Q
      (Root.state.reducedRow hReduced)
      (Root.state.reducedRetained hReduced) sigma i
```

at `Observation44RootProvenance.lean:616`.  It uses the whole fixed source row
as `uncontractedSegment`.  Its hit equivalence is the composition of strict
slice localization, exact reduced/root incidence, and the definitional
identification of root paths with `P.path` and `PseudoGrid.qPath`.

The initial recursive producer is:

```lean
theorem SimpleGraph.Exponent8
    .exists_initialRecursiveSliceLayer_of_pseudoGrid
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hDhat : 0 < Dhat)
    (hDscale : 2 * Dhat ≤ D)
    (hmass :
      2 * Gamma.rowPacking.card * wHat ≤ Dhat * w)
    (hXdisjoint :
      forall p : P.Index, Disjoint X (P.path p).vertexSet) :
    ∃ Root : RootedObservation44State Gamma,
      ∃ hReduced : Root.state.IsReduced,
        Nonempty
          (RecursiveSliceLayer
            G (Root.state.reducedGraph hReduced) A B X P Q
            (Root.state.reducedRow hReduced)
            (Root.state.reducedRetained hReduced)
            M w wHat Dhat)
```

at `statements-and-proofs/Exponent8/RootedSection42.lean:39`.  It depends on
the rooted reduced-state producer, `PathSlicing.theorem46`, the reduced
density theorem, `exists_additiveSliceCleanup`, and
`toSliceLocalizationInvariant_fullRows`.  It therefore returns actual cuts,
width, unique linkage, additive cleanup, and root localization for every
initial slice.

The source-level wrapper

```lean
Theorem41Setup.exists_initialRecursiveSliceLayer_of_pseudoGrid
```

at `RootedSection42.lean:169` discharges minimality, positive depth, and
`X`--main-path disjointness from the standing hypotheses of Theorem 4.1.

The old theorem
`section42_slicing_minor_of_pseudoGrid_actualPaths` existentially hides the
`Observation44State` and returns only `H`, `R`, and `Qpack`.  A theorem that
uses source-path provenance should call the rooted producer above rather than
attempt to recover it from that older output.

The declarations

```lean
PseudoGrid.goodQContactPackingInHPrime
PseudoGrid.goodQContactPackingInRowSupport
```

at `PseudoGridSlicing.lean:4234` and `:4281` replace each auxiliary path by a
length-zero row-contact path.  They are suitable for the older slicing
shortcut, but not for `LastHitCrossbar`.

## 11. Three-round recursive slicing interface

Module:

```text
statements-and-proofs/Exponent8/RecursiveSlicing.lean
```

This module is isolated from the polynomial-grid-minor aggregate.  It states
the target local threshold exactly as:

```lean
def SimpleGraph.Exponent8.exponentEightLocalThreshold
    (C logExp g : Nat) : Nat :=
  C * g^8 * Nat.sqrt g * (Nat.log 2 g + 1)^logExp
```

Location: `RecursiveSlicing.lean:46`.

The rounded internal fanout is `Nat.sqrt g + 1`; its equality and the
division-free square-root inequalities are fields of:

```lean
SimpleGraph.Exponent8.ThreeRoundParameters
```

at `RecursiveSlicing.lean:56`.

That structure also records:

- slice counts `m0`, `m1`, `m2`, `m3`;
- widths `w0`, `w1`, `w2`, `w3`;
- large-slice row thresholds `cap0`, `cap1`, `cap2`;
- the three majority-count recurrences;
- the three exact Theorem 4.6 budgets, including the `4 * g^4`
  Claim 5.3 loss;
- the large-branch assembly mass bounds;
- the final `8 * g^4 * (log + 1)` slice count;
- the final Lemma 4.8 pruning inequality; and
- the initial-cost inequality bounded by
  `exponentEightLocalThreshold C logExp g`.

### 11.1 Additive cleanup carried by each slice

Declarations:

```lean
SimpleGraph.Exponent8.AdditiveSliceCleanup
SimpleGraph.Exponent8.exists_additiveSliceCleanup
```

Locations: `RecursiveSlicing.lean:144` and `:175`.

`AdditiveSliceCleanup` retains the ordinary
`SliceIntersectingSubfamilies` fields and adds:

```lean
additive_loss :
  ((sigma.pathsInSlice Qbar i) \ paths).card * Dhat <=
    ((Finset.univ : Finset Rbar.Index) \ rows).card * wHat
```

The producer has the same density and cardinality hypotheses as the
one-slice Lemma 4.8 application:

```lean
noncomputable def exists_additiveSliceCleanup
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (sigma : PathSlicing Rbar M)
    (i : Fin M)
    (hDhat : 0 < Dhat)
    (hdense :
      forall q ∈ sigma.pathsInSlice Qbar i,
        2 * Dhat <=
          (sigma.segmentIntersectingLeftIndices Qbar i
            (Finset.univ : Finset Rbar.Index) q).card)
    (hcard :
      2 * Rbar.card * wHat <=
        Dhat * (sigma.pathsInSlice Qbar i).card) :
    AdditiveSliceCleanup sigma i wHat Dhat
```

It directly reuses
`PruneTrace.exists_intersecting_subsets_additive`; no recursive-slicing axiom
occurs in its closure.

### 11.2 Real recursive layer and Claim 5.3 bridge

Declaration:

```lean
SimpleGraph.Exponent8.RecursiveSliceLayer
```

Location: `RecursiveSlicing.lean:247`.

Each layer contains:

```lean
sigma : PathSlicing Rbar m
width_at_least : sigma.WidthAtLeast Qbar width
unique_linkage : Rbar.IsUniqueLinkage
cleanup : forall i : Fin m,
  AdditiveSliceCleanup sigma i wHat Dhat
localization : forall i : Fin m,
  SliceLocalizationInvariant
    G H A B X P Q Rbar Qbar sigma i
localized_eq : forall i,
  (localization i).localizedQ = (cleanup i).paths
```

The axiom-free consumer:

```lean
SimpleGraph.Exponent8.RecursiveSliceLayer.claim53Strong_cleanup
```

at `RecursiveSlicing.lean:280` takes a layer with
`wHat = 4 * g^2`, one slice, `0 < g`, and the absence of a width-`g^2`
crossbar.  It proves:

```lean
(L.cleanup i).paths.card <=
  ((L.localization i).goodQ
    ((Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows)
    (L.cleanup i).paths).card +
  4 * g^4
```

Thus the additive cleanup and strengthened Claim 5.3 are actually connected
before the placeholder.

### 11.3 The single named placeholder

The four possible recursive outcomes are represented by:

```lean
SimpleGraph.Exponent8.LargeSliceLayer
SimpleGraph.Exponent8.ThreeRoundRecursiveSlicingResult
```

at `RecursiveSlicing.lean:341` and `:364`.  The first three constructors are
majority-large exits at recursion depths zero, one, and two; the fourth
contains the final depth-three layer.

The only new project axiom is:

```lean
SimpleGraph.Exponent8.threeRoundRecursiveSlicing
```

at `RecursiveSlicing.lean:408`, with signature:

```lean
axiom threeRoundRecursiveSlicing
    ...
    (p : ThreeRoundParameters g Rbar.card Dhat)
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      p.m0 p.w0 (4 * g^2) Dhat)
    (hnoCrossbar :
      not Nonempty (Crossbar G A B X (g^2))) :
    Nonempty
      (ThreeRoundRecursiveSlicingResult
        G H A B X P Q Rbar Qbar g Dhat p L0)
```

The placeholder covers exactly:

1. Chuzhoy--Tan Observation 5.4's hereditary perfect-unique-linkage step;
2. composition of the local slice cuts into a global slicing;
3. propagating the now-produced `SliceLocalizationInvariant` through the
   three local refinements; and
4. the finite three-level majority/small-slice recursion.

It does not cover additive Lemma 4.8, LastHitCrossbar, the `O(g^4)` Claim 5.3
bound, their layer-level bridge, or Observation 4.4 root-incidence
provenance.

## 12. Trust baseline

The experimental audit file is:

```text
statements-and-proofs/Exponent8/AxiomAudit.lean
```

It audits the additive Lemma 4.8 declarations, finite last-hit selection,
LastHitCrossbar, rooted Observation 4.4 incidence and localization,
strengthened Claim 5.3, the additive per-slice producer, and the
recursive-layer Claim 5.3 bridge.

A focused audit of the following existing declarations was also run:

```text
SimpleGraph.PathSlicing.theorem46
SimpleGraph.PathSlicing.linkageOrderingOfUnique
SimpleGraph.PathPacking.exists_intersecting_path_subfamilies
SimpleGraph.FiniteBipartitePruning.PruneTrace.deleted_right_mul_le_deleted_left_mul
SimpleGraph.Section44.PathPacking.theorem411
SimpleGraph.Section45.theorem415
SimpleGraph.PseudoGrid.rowPerfectPackingInRowSupport_isUniqueLinkage
SimpleGraph.PseudoGrid.observation_four_four_unique_linkage_reduction
```

Each reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No proved declaration above depends on a project-specific axiom.  The sole
non-proved declaration is the explicitly named
`SimpleGraph.Exponent8.threeRoundRecursiveSlicing`, whose audit reports
itself in addition to the standard Lean axioms.  Every theorem preceding that
placeholder reports only `propext`, `Classical.choice`, and `Quot.sound`
(some arithmetic lemmas use a subset of these).

Run the isolated audit with:

```bash
lake env lean statements-and-proofs/Exponent8/AxiomAudit.lean
```
