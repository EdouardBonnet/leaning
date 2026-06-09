import Chapter01.definitions_ch1
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Tactic

set_option linter.all false

open scoped BigOperators

universe u v

namespace Diestel
namespace Chapter02

open Diestel.Chapter01

variable {V : Type u} {W : Type v}

/-- A finite family of non-empty, pairwise disjoint sets covering all vertices. -/
def IsVertexPartition (P : Finset (Set V)) : Prop :=
  (∀ U ∈ P, U.Nonempty) ∧
    (∀ U ∈ P, ∀ W ∈ P, U ≠ W → Disjoint U W) ∧
      ∀ v : V, ∃ U ∈ P, v ∈ U

/-- Diestel multigraphs use Mathlib's multigraph type. -/
abbrev MultiGraph (V : Type u) (E : Type v) := Graph V E

namespace MultiGraph

/-- A vertex partition of a specified vertex set. -/
def IsVertexPartitionOf (X : Set V) (P : Finset (Set V)) : Prop :=
  (∀ U ∈ P, U.Nonempty ∧ U ⊆ X) ∧
    (∀ U ∈ P, ∀ W ∈ P, U ≠ W → Disjoint U W) ∧
      ∀ v : V, v ∈ X → ∃ U ∈ P, v ∈ U

/-- Diestel's multigraphs are loopless; Mathlib's `Graph` also permits loops. -/
def Loopless (G : MultiGraph V E) : Prop :=
  ∀ ⦃e : E⦄, e ∈ G.edgeSet → ∀ x : V, ¬ G.IsLoopAt e x

/-- The simple graph obtained by forgetting parallel edges. -/
def toSimpleGraph (G : MultiGraph V E) : SimpleGraph G.vertexSet where
  Adj x y := x ≠ y ∧ G.Adj x.1 y.1
  symm := by
    rintro x y ⟨hxy, hadj⟩
    exact ⟨fun hyx => hxy hyx.symm, hadj.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Connectedness of a multigraph, through its underlying simple graph. -/
def Connected (G : MultiGraph V E) : Prop :=
  G.toSimpleGraph.Connected

/-- Edge `e` is incident with vertex `v`. -/
def Incident (G : MultiGraph V E) (v : V) (e : E) : Prop :=
  e ∈ G.edgeSet ∧ G.Inc e v

/-- The degree of a vertex, counting parallel edges. -/
noncomputable def degree (G : MultiGraph V E) [Finite E] (v : V) : ℕ :=
  Nat.card {e : E // G.Incident v e}

/-- `G` is regular of degree `k`, counting parallel edges. -/
def IsRegularOfDegree (G : MultiGraph V E) [Finite E] (k : ℕ) : Prop :=
  ∀ v : V, v ∈ G.vertexSet → G.degree v = k

/-- A cubic multigraph is a 3-regular multigraph. -/
abbrev IsCubic (G : MultiGraph V E) [Finite E] : Prop :=
  G.Loopless ∧ G.IsRegularOfDegree 3

/-- The simple graph shadow of a selected edge set. -/
def edgeSubgraph (G : MultiGraph V E) (F : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e : E, e ∈ F ∧ e ∈ G.edgeSet ∧ G.IsLink e x y
  symm := by
    rintro x y ⟨hxy, e, heF, heG, hlink⟩
    exact ⟨fun hyx => hxy hyx.symm, e, heF, heG, hlink.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Vertices incident with at least one edge in `F`. -/
def edgeVertexSet (G : MultiGraph V E) (F : Set E) : Set V :=
  {v | ∃ e ∈ F, e ∈ G.edgeSet ∧ G.Inc e v}

/-- A selected edge set forms a tree on its incident vertices. -/
def IsTree (G : MultiGraph V E) (F : Set E) : Prop :=
  F.Finite ∧ F ⊆ G.edgeSet ∧
    ((G.edgeSubgraph F).induce (G.edgeVertexSet F)).Connected ∧
    F.ncard + 1 = (G.edgeVertexSet F).ncard

/-- A selected edge set forms a spanning tree of the multigraph. -/
def IsSpanningTree (G : MultiGraph V E) (F : Set E) : Prop :=
  F.Finite ∧ F ⊆ G.edgeSet ∧
    ((G.vertexSet = ∅ ∧ F = ∅) ∨
      ((G.edgeSubgraph F).induce G.vertexSet).Connected ∧ F.ncard + 1 = G.vertexSet.ncard)

/-- A family of edge sets is pairwise edge-disjoint. -/
def EdgeDisjointFamily {ι : Type w} (T : ι → Set E) : Prop :=
  Pairwise fun i j => Disjoint (T i) (T j)

/-- A family of selected edge sets is a family of spanning trees. -/
def FamilySpanningTrees {ι : Type w} (G : MultiGraph V E) (T : ι → Set E) : Prop :=
  ∀ i : ι, G.IsSpanningTree (T i)

/-- The set of all edges appearing in a family. -/
def FamilyEdgeSet {ι : Type w} (T : ι → Set E) : Set E :=
  {e | ∃ i : ι, e ∈ T i}

/-- Every edge of `G` is covered by the family `T`. -/
def EdgeCoveredByFamily {ι : Type w} (G : MultiGraph V E) (T : ι → Set E) : Prop :=
  ∀ e : E, e ∈ G.edgeSet → ∃ i : ι, e ∈ T i

/-- `G` has `k` pairwise edge-disjoint spanning trees. -/
def HasKEdgeDisjointSpanningTrees (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ T : Fin k → Set E, G.FamilySpanningTrees T ∧ EdgeDisjointFamily T

/-- The edges of `G` can be covered by at most `k` spanning trees. -/
def CanCoverEdgesByAtMostKSpanningTrees (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ k ∧ ∃ T : Fin n → Set E,
    G.FamilySpanningTrees T ∧ G.EdgeCoveredByFamily T

/-- `G` remains connected after deleting any set of fewer than `l` edges. -/
def IsLEdgeConnected (G : MultiGraph V E) (l : ℕ) : Prop :=
  ∀ F : Set E, F.Finite → F ⊆ G.edgeSet → F.ncard < l →
    ((G.edgeSubgraph (G.edgeSet \ F)).induce G.vertexSet).Connected

/-- Edges with one end in `U` and the other end outside `U`. -/
def edgeBoundary (G : MultiGraph V E) (U : Set V) : Set E :=
  {e | e ∈ G.edgeSet ∧ ∃ x y : V, G.IsLink e x y ∧ x ∈ U ∧ y ∈ G.vertexSet ∧ y ∉ U}

/-- The edges of `G` whose endpoints both lie in `U`. -/
def EdgeSetInside (G : MultiGraph V E) (U : Set V) : Set E :=
  {e | e ∈ G.edgeSet ∧ ∀ v : V, G.Inc e v → v ∈ U}

/-- The number of multiedges induced by `U`, counting parallel edges. -/
noncomputable def inducedEdgeCount (G : MultiGraph V E) [Finite E] (U : Set V) : ℕ :=
  Nat.card {e : E // e ∈ G.EdgeSetInside U}

/-- An edge crosses a vertex partition if its endpoints lie in different classes. -/
def IsCrossEdge (G : MultiGraph V E) (P : Finset (Set V)) (e : E) : Prop :=
  e ∈ G.edgeSet ∧ ∃ x y : V, G.IsLink e x y ∧
    ∃ U ∈ P, ∃ W ∈ P, U ≠ W ∧ x ∈ U ∧ y ∈ W

/-- The number of partition-crossing multiedges, counting parallel edges. -/
noncomputable def crossEdgeCount (G : MultiGraph V E) [Finite E]
    (P : Finset (Set V)) : ℕ :=
  Nat.card {e : E // G.IsCrossEdge P e}

/-- A cycle in a multigraph, represented as a connected 2-regular edge set. -/
structure CycleIn (G : MultiGraph V E) where
  support : Set V
  edgeSupport : Set E
  edgeSupport_finite : edgeSupport.Finite
  edges_inside : edgeSupport ⊆ G.EdgeSetInside support
  support_nonempty : support.Nonempty
  connected : ((G.edgeSubgraph edgeSupport).induce support).Connected
  degree_two : ∀ v : V, v ∈ support →
    Nat.card {e : edgeSupport // G.Inc e.1 v} = 2

/-- `G` contains `k` pairwise vertex-disjoint cycles. -/
def HasKDisjointCycles (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ C : Fin k → CycleIn G, Pairwise fun i j => Disjoint (C i).support (C j).support

/--
A selected edge set is a forest in the multigraph sense. This is the
right edge-set trace of a tree covering: Diestel allows the covering trees
themselves not to be subgraphs of `G`, so their edges inside `G` need only
form forests. The cycle condition is stated for multigraph cycles, since a
simple shadow would miss parallel-edge 2-cycles.
-/
def IsForest (G : MultiGraph V E) (F : Set E) : Prop :=
  F.Finite ∧ F ⊆ G.edgeSet ∧
    (∀ e : E, e ∈ F → ∀ x : V, ¬ G.IsLoopAt e x) ∧
      ∀ C : CycleIn G, ¬ C.edgeSupport ⊆ F

/-- The edges of `G` can be covered by at most `k` acyclic edge traces. -/
def CanCoverEdgesByAtMostKTrees (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ k ∧ ∃ T : Fin n → Set E,
    (∀ i : Fin n, G.IsForest (T i)) ∧ G.EdgeCoveredByFamily T

/-- A selected edge set is a spanning tree of the subgraph induced by `U`. -/
def IsSpanningTreeOn (G : MultiGraph V E) (U : Set V) (F : Set E) : Prop :=
  U ⊆ G.vertexSet ∧ F.Finite ∧ F ⊆ G.EdgeSetInside U ∧
    ((U = ∅ ∧ F = ∅) ∨
      ((G.edgeSubgraph F).induce U).Connected ∧
        F.ncard + 1 = U.ncard)

/-- The subgraph induced by `U` has `k` pairwise edge-disjoint spanning trees. -/
def HasKEdgeDisjointSpanningTreesOn (G : MultiGraph V E) (U : Set V) (k : ℕ) : Prop :=
  ∃ T : Fin k → Set E, (∀ i : Fin k, G.IsSpanningTreeOn U (T i)) ∧
    EdgeDisjointFamily T

/-- The subtype of edges crossing a fixed vertex partition. -/
abbrev CrossEdge (G : MultiGraph V E) (P : Finset (Set V)) :=
  {e : E // G.IsCrossEdge P e}

/-- The quotient graph shadow on partition classes, retaining crossing multiedges as edge labels. -/
def quotientEdgeSubgraph (G : MultiGraph V E) (P : Finset (Set V))
    (F : Set (G.CrossEdge P)) : SimpleGraph {U : Set V // U ∈ P} where
  Adj U W := U ≠ W ∧
    ∃ e : G.CrossEdge P, e ∈ F ∧
      ∃ x ∈ U.1, ∃ y ∈ W.1, G.IsLink e.1 x y
  symm := by
    rintro U W ⟨hne, e, heF, x, hx, y, hy, hxy⟩
    exact ⟨fun h => hne h.symm, e, heF, y, hy, x, hx, hxy.symm⟩
  loopless := ⟨fun U h => h.1 rfl⟩

/-- A quotient edge set forms a spanning tree on the partition classes. -/
def IsQuotientSpanningTree (G : MultiGraph V E) (P : Finset (Set V))
    (F : Set (G.CrossEdge P)) : Prop :=
  F.Finite ∧
    ((P = ∅ ∧ F = ∅) ∨
      (G.quotientEdgeSubgraph P F).Connected ∧ F.ncard + 1 = P.card)

/-- The quotient's crossing edges are covered by `k` spanning trees. -/
def QuotientEdgesCoveredByKSpanningTrees (G : MultiGraph V E) (P : Finset (Set V))
    (k : ℕ) : Prop :=
  ∃ T : Fin k → Set (G.CrossEdge P),
    (∀ i : Fin k, G.IsQuotientSpanningTree P (T i)) ∧
      ∀ e : G.CrossEdge P, ∃ i : Fin k, e ∈ T i

/-- The Bowler-Carmesin packing-covering conclusion for a multigraph partition. -/
def PackingCoveringPartition (G : MultiGraph V E) (P : Finset (Set V)) (k : ℕ) : Prop :=
  IsVertexPartitionOf G.vertexSet P ∧
    (∀ U ∈ P, G.HasKEdgeDisjointSpanningTreesOn U k) ∧
      G.QuotientEdgesCoveredByKSpanningTrees P k

/-- An edge lies in at least two distinct members of a tree family. -/
def EdgeInAtLeastTwoTrees {ι : Type w} (T : ι → Set E) (e : E) : Prop :=
  ∃ i j : ι, i ≠ j ∧ e ∈ T i ∧ e ∈ T j

/-- One exchange step replacing `e` by `f` in one spanning tree of the family. -/
def IsExchangeStep {ι : Type w} (G : MultiGraph V E) (T : ι → Set E) (e f : E) : Prop :=
  ∃ i : ι, G.IsSpanningTree (T i) ∧ e ∈ T i ∧ f ∉ T i ∧
    G.IsSpanningTree (((T i) ∪ {f}) \ {e})

/-- `e` starts an exchange chain ending at an edge outside all trees. -/
def StartsExchangeChain {ι : Type w} (G : MultiGraph V E) (T : ι → Set E) (e : E) : Prop :=
  ∃ f : E, f ∉ FamilyEdgeSet T ∧
    Relation.ReflTransGen (fun a b => G.IsExchangeStep T a b) e f

/-- A family of spanning trees can be improved by strictly increasing its edge union. -/
def CanImproveTreeFamily {ι : Type w} (G : MultiGraph V E) (T : ι → Set E) : Prop :=
  ∃ T' : ι → Set E, G.FamilySpanningTrees T' ∧ FamilyEdgeSet T ⊂ FamilyEdgeSet T'

end MultiGraph

/-- Chapter 1's cubic-graph predicate, re-exported for Chapter 2 statements. -/
abbrev IsCubic (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  Diestel.Chapter01.IsCubic G

/-- Chapter 1's edge-connectivity predicate, re-exported for Chapter 2 statements. -/
abbrev IsLEdgeConnected (G : SimpleGraph V) [Finite V] (l : ℕ) : Prop :=
  Diestel.Chapter01.IsLEdgeConnected G l

/-- The maximum size of a matching in a finite graph. -/
noncomputable def matchingNumber (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : ℕ :=
  let p : ℕ → Prop := fun n => ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card M.edgeSet = n
  letI := Classical.decPred p
  Nat.findGreatest p G.edgeFinset.card

/-- `M` is a matching covering every vertex of `A`. -/
def HasMatchingOf (G : SimpleGraph V) (A : Set V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ A ⊆ M.verts

/-- Neighbours of `S` that lie in the specified opposite side `B`. -/
def neighboursIn (G : SimpleGraph V) (S B : Set V) : Set V :=
  (⋃ v ∈ S, G.neighborSet v) ∩ B

/-- Hall's marriage condition for a bipartite graph with left side `A`. -/
def MarriageCondition (G : SimpleGraph V) [Finite V] (A B : Set V) : Prop :=
  ∀ S : Set V, S ⊆ A → S.ncard ≤ (neighboursIn G S B).ncard

/-- A spanning `k`-regular subgraph of `G`, i.e. Diestel's `k`-factor. -/
def HasKFactor (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v : V, Nat.card (H.neighborSet v) = k

/-- The edges of `G` incident with `v`. -/
abbrev IncidentEdge (G : SimpleGraph V) (v : V) :=
  {e : G.edgeSet // v ∈ (e : Sym2 V)}

/-- A family of strict linear preferences on the incident edges of each vertex. -/
structure Preferences (G : SimpleGraph V) where
  lt : ∀ v : V, IncidentEdge G v → IncidentEdge G v → Prop
  strictTotal : ∀ v : V, IsStrictTotalOrder (IncidentEdge G v) (lt v)

/--
A stable matching for a preference profile: every non-matching edge is
blocked at one of its ends by that vertex's current matching edge.
-/
def StableMatching (G : SimpleGraph V) (P : Preferences G) (M : G.Subgraph) : Prop :=
  M.IsMatching ∧
    ∀ e : G.edgeSet, (e : Sym2 V) ∉ M.edgeSet →
      ∃ f : G.edgeSet, (f : Sym2 V) ∈ M.edgeSet ∧
        ∃ v : V, ∃ he : v ∈ (e : Sym2 V), ∃ hf : v ∈ (f : Sym2 V),
          P.lt v ⟨e, he⟩ ⟨f, hf⟩

/-- Delete one vertex by inducing on its complement. -/
abbrev deleteVertex (G : SimpleGraph V) (v : V) : SimpleGraph ({w : V | w ≠ v}) :=
  G.induce ({w : V | w ≠ v} : Set V)

/-- A non-empty graph that becomes perfectly matchable after deleting any one vertex. -/
def IsFactorCritical (G : SimpleGraph V) [Finite V] : Prop :=
  Nonempty V ∧
    (∀ M : G.Subgraph, ¬ M.IsPerfectMatching) ∧
      ∀ v : V, ∃ M : (deleteVertex G v).Subgraph, M.IsPerfectMatching

/-- Tutte's condition: no set of deleted vertices leaves too many odd components. -/
def TutteCondition (G : SimpleGraph V) [Finite V] : Prop :=
  ∀ S : Set V, ¬ G.IsTutteViolator S

/-- Components of `G - S`, represented in Mathlib as components of the induced complement. -/
abbrev DeletedComponent (G : SimpleGraph V) (S : Set V) :=
  (delete_vertices G S).ConnectedComponent

/-- `S` can be matched injectively to components of `G - S` by incident edges. -/
def MatchableToDeletedComponents (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ f : S → DeletedComponent G S, Function.Injective f ∧
    ∀ s : S, ∃ x : (f s).supp, G.Adj s.1 x.1.1

/-- The two structural properties of the Gallai-Edmonds set from Theorem 2.2.3. -/
def GallaiEdmondsSet (G : SimpleGraph V) [Finite V] (S : Set V) : Prop :=
  MatchableToDeletedComponents G S ∧
    ∀ C : DeletedComponent G S, IsFactorCritical C.toSimpleGraph

/-- A graph with no bridges. -/
def IsBridgeless (G : SimpleGraph V) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → ¬ G.IsBridge e

/-- A concrete cycle in a graph, represented by a cyclic walk. -/
structure CycleIn (G : SimpleGraph V) where
  root : V
  walk : G.Walk root root
  isCycle : walk.IsCycle

namespace CycleIn

/-- The vertex set of a concrete cycle. -/
def support {G : SimpleGraph V} (C : CycleIn G) : Set V :=
  {v | v ∈ C.walk.support}

end CycleIn

/-- `G` contains `k` pairwise vertex-disjoint cycles. -/
def HasKDisjointCycles (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ C : Fin k → CycleIn G, Pairwise fun i j => Disjoint (C i).support (C j).support

/-- A vertex set meeting every cycle of `G`. -/
def IsCycleVertexCover (G : SimpleGraph V) (U : Set V) : Prop :=
  ∀ C : CycleIn G, ((C.support) ∩ U).Nonempty

/-- A function `f` is an Erdos-Posa bound for cycle packing versus vertex covering. -/
def ErdosPosaCycleBound (f : ℕ → ℕ) : Prop :=
  ∀ ⦃V : Type u⦄ (G : SimpleGraph V) [Fintype V] [DecidableEq V]
      [DecidableRel G.Adj] (k : ℕ),
    HasKDisjointCycles G k ∨ ∃ U : Set V, U.ncard ≤ f k ∧ IsCycleVertexCover G U

/-- Diestel's auxiliary `r_k = log k + log log k + 4`, with logarithms base two. -/
noncomputable def erdosPosaR (k : ℕ) : ℝ :=
  (Real.log (k : ℝ) / Real.log 2) +
    (Real.log (Real.log (k : ℝ) / Real.log 2) / Real.log 2) + 4

/-- Diestel's auxiliary threshold `s_k` used in Lemma 2.3.1. -/
noncomputable def erdosPosaS (k : ℕ) : ℝ :=
  if 2 ≤ k then 4 * (k : ℝ) * erdosPosaR k else 1

/-- An edge crosses a vertex partition if its ends lie in different partition classes. -/
def IsCrossEdge (G : SimpleGraph V) (P : Finset (Set V)) (e : Sym2 V) : Prop :=
  ∃ x y : V, ∃ U ∈ P, ∃ W ∈ P,
    U ≠ W ∧ x ∈ U ∧ y ∈ W ∧ e = s(x, y)

/-- The number of cross-edges of `G` with respect to a finite vertex partition. -/
noncomputable def crossEdgeCount (G : SimpleGraph V) (P : Finset (Set V)) : ℕ :=
  Nat.card {e : G.edgeSet // IsCrossEdge G P (e : Sym2 V)}

/-- A family of graphs has pairwise disjoint edge sets. -/
def EdgeDisjointFamily {ι : Type v} (T : ι → SimpleGraph V) : Prop :=
  Pairwise fun i j => Disjoint (T i).edgeSet (T j).edgeSet

/-- A family of spanning trees of `G`. -/
def FamilySpanningTrees {ι : Type v} (G : SimpleGraph V) (T : ι → SimpleGraph V) : Prop :=
  ∀ i : ι, IsSpanningTree G (T i)

/-- `G` has `k` edge-disjoint spanning trees. -/
def HasKEdgeDisjointSpanningTrees (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ T : Fin k → SimpleGraph V, FamilySpanningTrees G T ∧ EdgeDisjointFamily T

/-- The edges covered by a family of subgraphs. -/
def EdgeCoveredByFamily {ι : Type v} (G : SimpleGraph V) (T : ι → SimpleGraph V) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → ∃ i : ι, e ∈ (T i).edgeSet

/--
`G` has its edges covered by at most `k` acyclic subgraphs. These are the
edge traces in `G` of Diestel's covering trees.
-/
def CanCoverEdgesByAtMostKTrees (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ k ∧ ∃ T : Fin n → SimpleGraph V,
    (∀ i : Fin n, T i ≤ G ∧ (T i).IsAcyclic) ∧ EdgeCoveredByFamily G T

/-- `G` has its edges covered by at most `k` spanning-tree subgraphs. -/
def CanCoverEdgesByAtMostKSpanningTrees (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ k ∧ ∃ T : Fin n → SimpleGraph V,
    FamilySpanningTrees G T ∧ EdgeCoveredByFamily G T

/-- `G` has its edges covered by `k` spanning-tree subgraphs. -/
def CanCoverEdgesByKSpanningTrees (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ T : Fin k → SimpleGraph V, FamilySpanningTrees G T ∧ EdgeCoveredByFamily G T

/-- The number of edges induced by a vertex set. -/
noncomputable def inducedEdgeCount (G : SimpleGraph V) (U : Set V) : ℕ :=
  Nat.card (G.induce U).edgeSet

/-- The simple quotient graph on the classes of a finite vertex partition. -/
def quotientGraphByPartition (G : SimpleGraph V) (P : Finset (Set V)) :
    SimpleGraph {U : Set V // U ∈ P} where
  Adj U W := U ≠ W ∧ ∃ u ∈ U.1, ∃ w ∈ W.1, G.Adj u w
  symm := by
    rintro U W ⟨hne, u, hu, w, hw, huw⟩
    exact ⟨fun h => hne h.symm, w, hw, u, hu, huw.symm⟩
  loopless := ⟨fun U h => h.1 rfl⟩

/-- The Bowler-Carmesin packing-covering conclusion for a partition. -/
def PackingCoveringPartition (G : SimpleGraph V) (P : Finset (Set V)) (k : ℕ) : Prop :=
  IsVertexPartition P ∧
    (∀ U ∈ P, HasKEdgeDisjointSpanningTrees (G.induce U) k) ∧
      CanCoverEdgesByKSpanningTrees (quotientGraphByPartition G P) k

/-- The set of all edges appearing in a family of trees. -/
def FamilyEdgeSet {ι : Type v} (T : ι → SimpleGraph V) : Set (Sym2 V) :=
  {e | ∃ i : ι, e ∈ (T i).edgeSet}

/-- An edge lies in at least two distinct members of a tree family. -/
def EdgeInAtLeastTwoTrees {ι : Type v} (T : ι → SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ i j : ι, i ≠ j ∧ e ∈ (T i).edgeSet ∧ e ∈ (T j).edgeSet

/-- One step in an exchange chain with respect to a family of spanning trees. -/
def IsExchangeStep {ι : Type v} (G : SimpleGraph V) (T : ι → SimpleGraph V)
    (e f : G.edgeSet) : Prop :=
  ∃ i : ι, ∃ a : V, ∃ c : G.Walk a a,
    IsSpanningTree G (T i) ∧
      IsTreeChord G (T i) (f : Sym2 V) ∧
        IsFundamentalCycle G (T i) (f : Sym2 V) c ∧ (e : Sym2 V) ∈ c.edgeSet

/-- `e` starts an exchange chain ending at an edge outside all trees of the family. -/
def StartsExchangeChain {ι : Type v} (G : SimpleGraph V) (T : ι → SimpleGraph V)
    (e : G.edgeSet) : Prop :=
  ∃ f : G.edgeSet, (f : Sym2 V) ∉ FamilyEdgeSet T ∧
    Relation.ReflTransGen (IsExchangeStep G T) e f

/-- A family of spanning trees can be improved by strictly increasing its edge union. -/
def CanImproveTreeFamily {ι : Type v} (G : SimpleGraph V) (T : ι → SimpleGraph V) : Prop :=
  ∃ T' : ι → SimpleGraph V,
    FamilySpanningTrees G T' ∧ FamilyEdgeSet T ⊂ FamilyEdgeSet T'

/-- A directed graph, represented by its adjacency relation. -/
abbrev DirectedGraph (V : Type u) := V → V → Prop

/-- A list whose consecutive entries follow the directed edges. -/
def IsDirectedWalkList (D : DirectedGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | x :: y :: zs => D x y ∧ IsDirectedWalkList D (y :: zs)

/-- A directed path is a non-empty directed walk list with no repeated vertices. -/
def IsDirectedPath (D : DirectedGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p ≠ [] ∧ IsDirectedWalkList D p

/-- The vertex set of a list path. -/
def listVertexSet (p : List V) : Set V :=
  {v | v ∈ p}

/-- Independence in a directed graph: no directed edge between distinct vertices in either direction. -/
def DirectedIndependentSet (D : DirectedGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → x ≠ y → ¬ D x y ∧ ¬ D y x

/-- A finite set of vertex-disjoint directed paths covering all vertices. -/
def IsDirectedPathCover (D : DirectedGraph V) (P : Finset (List V)) : Prop :=
  (∀ p ∈ P, IsDirectedPath D p) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (listVertexSet p) (listVertexSet q)) ∧
      ∀ v : V, ∃ p ∈ P, v ∈ p

/-- A Gallai-Milgram path cover with independent representatives. -/
def HasIndependentPathCoverRepresentatives (D : DirectedGraph V) : Prop :=
  ∃ P : Finset (List V), IsDirectedPathCover D P ∧
    ∃ rep : {p : List V // p ∈ P} → V,
      (∀ p, rep p ∈ p.1) ∧ DirectedIndependentSet D (Set.range rep)

/-- A finite chain in a partial order. -/
def IsChainFinset (C : Finset V) [LE V] : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x

/-- A finite antichain in a partial order. -/
def IsAntichainFinset (A : Finset V) [LE V] : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y ∧ ¬ y ≤ x

/-- A cover of a finite ordered set by `n` chains. -/
def ChainCover (V : Type u) [LE V] [Fintype V] (n : ℕ) : Prop :=
  ∃ C : Fin n → Finset V, (∀ i : Fin n, IsChainFinset (C i)) ∧
    ∀ x : V, ∃ i : Fin n, x ∈ C i

/-- The maximum cardinality of an antichain in a finite ordered set. -/
noncomputable def maxAntichainCard (V : Type u) [LE V] [Fintype V] : ℕ :=
  let p : ℕ → Prop := fun n => ∃ A : Finset V, IsAntichainFinset A ∧ A.card = n
  letI := Classical.decPred p
  Nat.findGreatest p (Fintype.card V)

end Chapter02
end Diestel
