import «statements-and-proofs».Exponent7.CutResponder.RoundFamilyAuxGraph
import «statements-and-proofs».MinorContract

/-!
# A clean round family as a host minor

This module is independent of the strong path-of-sets construction.  It gives
the generic branch-set conversion used by the cut-responder consumer.

Each abstract coordinate has a node-disjoint host row.  Each matching edge has
a host path joining its two endpoint rows.  The edge paths are mutually
node-disjoint and internally avoid the union of all coordinate rows.  We
allocate the drop-last part of every edge path to its source coordinate.  Its
final edge then witnesses adjacency to the target branch set.
-/

namespace SimpleGraph
namespace CutMatchingGame

universe u v

open Finset

variable {V : Type u} {X : Type v}
variable [Fintype V] [DecidableEq V]
variable [Fintype X] [DecidableEq X]
variable {G : _root_.SimpleGraph V}

namespace RoundFamily

/-- The union of all coordinate-row vertex sets. -/
noncomputable def rowVertexSet
    (rows : X → GraphPath G) : Finset V :=
  (Finset.univ : Finset X).biUnion fun x => (rows x).vertexSet

theorem mem_rowVertexSet
    (rows : X → GraphPath G) (x : X) {v : V}
    (hv : v ∈ (rows x).vertexSet) :
    v ∈ rowVertexSet rows := by
  classical
  rw [rowVertexSet]
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hv⟩

/-- A clean geometric realization of every edge of a round family. -/
structure HostRealization
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (rows : X → GraphPath G) where
  row_nodeDisjoint :
    Pairwise fun x y => GraphPath.NodeDisjoint (rows x) (rows y)
  edgePath : F.Edge → GraphPath G
  edgePath_source_mem :
    ∀ e, (edgePath e).source ∈ (rows (F.edgeSource e)).vertexSet
  edgePath_target_mem :
    ∀ e, (edgePath e).target ∈ (rows (F.edgeTarget e)).vertexSet
  edgePath_nodeDisjoint :
    Pairwise fun e f => GraphPath.NodeDisjoint (edgePath e) (edgePath f)
  edgePath_internallyDisjoint_rows :
    ∀ e, (edgePath e).InternallyDisjointFromSet (rowVertexSet rows)

namespace HostRealization

variable {roundBound : ℕ}
variable {F : RoundFamily X (Fin roundBound)}
variable {rows : X → GraphPath G}

/-- An edge path is nontrivial because its endpoint rows are distinct. -/
theorem edgePath_source_ne_target
    (R : HostRealization F rows) (e : F.Edge) :
    (R.edgePath e).source ≠ (R.edgePath e).target := by
  intro h
  have hs :
      (R.edgePath e).source ∈
        (rows (F.edgeSource e)).vertexSet :=
    R.edgePath_source_mem e
  have ht :
      (R.edgePath e).source ∈
        (rows (F.edgeTarget e)).vertexSet := by
    simpa [h] using R.edgePath_target_mem e
  exact
    Finset.disjoint_left.mp
      (R.row_nodeDisjoint (F.edgeSource_ne_edgeTarget e))
      hs ht

/-- The source endpoint belongs to the half-open edge-path support. -/
theorem edgePath_source_mem_dropLast
    (R : HostRealization F rows) (e : F.Edge) :
    (R.edgePath e).source ∈ (R.edgePath e).dropLast.vertexSet := by
  simpa using GraphPath.source_mem_vertexSet (R.edgePath e).dropLast

/-- The final edge of a realized matching path. -/
theorem edgePath_penultimate_adj_target
    (R : HostRealization F rows) (e : F.Edge) :
    G.Adj (R.edgePath e).penultimate (R.edgePath e).target :=
  (R.edgePath e).penultimate_adj_target (R.edgePath_source_ne_target e)

/-- Allocate the complete coordinate row and every outgoing half-open matching
path to the source coordinate. -/
noncomputable def sourceAllocatedBranchSet
    (R : HostRealization F rows) (x : X) : Finset V :=
  (rows x).vertexSet ∪
    (Finset.univ.biUnion fun e : F.Edge =>
      if F.edgeSource e = x then
        (R.edgePath e).dropLast.vertexSet
      else
        ∅)

theorem row_subset_sourceAllocatedBranchSet
    (R : HostRealization F rows) (x : X) :
    (rows x).vertexSet ⊆ R.sourceAllocatedBranchSet x := by
  intro v hv
  exact Finset.mem_union_left _ hv

theorem mem_sourceAllocatedBranchSet_iff
    (R : HostRealization F rows) {x : X} {v : V} :
    v ∈ R.sourceAllocatedBranchSet x ↔
      v ∈ (rows x).vertexSet ∨
        ∃ e : F.Edge, F.edgeSource e = x ∧
          v ∈ (R.edgePath e).dropLast.vertexSet := by
  classical
  rw [sourceAllocatedBranchSet, Finset.mem_union]
  constructor
  · intro hv
    rcases hv with hvRow | hvEdge
    · exact Or.inl hvRow
    · rw [Finset.mem_biUnion] at hvEdge
      rcases hvEdge with ⟨e, _he, hvIf⟩
      by_cases hsource : F.edgeSource e = x
      · exact Or.inr ⟨e, hsource, by simpa [hsource] using hvIf⟩
      · simp [hsource] at hvIf
  · rintro (hvRow | ⟨e, hsource, hvDrop⟩)
    · exact Or.inl hvRow
    · exact Or.inr <|
        Finset.mem_biUnion.mpr
          ⟨e, Finset.mem_univ e, by
            change v ∈
              (if F.edgeSource e = x then
                (R.edgePath e).dropLast.vertexSet
              else ∅)
            simpa [hsource] using hvDrop⟩

theorem dropLast_subset_sourceAllocatedBranchSet
    (R : HostRealization F rows) (e : F.Edge) :
    (R.edgePath e).dropLast.vertexSet ⊆
      R.sourceAllocatedBranchSet (F.edgeSource e) := by
  intro v hv
  rw [R.mem_sourceAllocatedBranchSet_iff]
  exact Or.inr ⟨e, rfl, hv⟩

theorem sourceAllocatedBranchSet_nonempty
    (R : HostRealization F rows) (x : X) :
    (R.sourceAllocatedBranchSet x).Nonempty := by
  exact
    ⟨(rows x).source,
      R.row_subset_sourceAllocatedBranchSet x
        (GraphPath.source_mem_vertexSet (rows x))⟩

/-- A half-open realized edge path allocated to `x` avoids every other
coordinate row. -/
theorem dropLast_disjoint_row_of_source_ne
    (R : HostRealization F rows)
    (e : F.Edge) {x y : X}
    (hsource : F.edgeSource e = x) (hxy : x ≠ y) :
    Disjoint (R.edgePath e).dropLast.vertexSet (rows y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvDrop hvRow
  have hvPath :
      v ∈ (R.edgePath e).vertexSet :=
    (R.edgePath e).dropLast_vertexSet_subset hvDrop
  have hvAll : v ∈ rowVertexSet rows :=
    mem_rowVertexSet rows y hvRow
  rcases R.edgePath_internallyDisjoint_rows e hvPath hvAll with
    hvSource | hvTarget
  · subst v
    have hs :
        (R.edgePath e).source ∈ (rows x).vertexSet := by
      simpa [hsource] using R.edgePath_source_mem e
    exact
      Finset.disjoint_left.mp (R.row_nodeDisjoint hxy) hs hvRow
  · subst v
    exact
      (R.edgePath e).target_not_mem_dropLast_vertexSet
        (R.edgePath_source_ne_target e) hvDrop

/-- Half-open edge supports allocated to different source coordinates are
disjoint. -/
theorem dropLast_disjoint_dropLast_of_sources_ne
    (R : HostRealization F rows)
    (e f : F.Edge) {x y : X}
    (he : F.edgeSource e = x)
    (hf : F.edgeSource f = y)
    (hxy : x ≠ y) :
    Disjoint (R.edgePath e).dropLast.vertexSet
      (R.edgePath f).dropLast.vertexSet := by
  have hef : e ≠ f := by
    intro hef
    apply hxy
    rw [← he, ← hf, hef]
  exact
    (R.edgePath_nodeDisjoint hef).mono
      (R.edgePath e).dropLast_vertexSet_subset
      (R.edgePath f).dropLast_vertexSet_subset

theorem sourceAllocatedBranchSet_disjoint
    (R : HostRealization F rows)
    {x y : X} (hxy : x ≠ y) :
    Disjoint (R.sourceAllocatedBranchSet x)
      (R.sourceAllocatedBranchSet y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  rw [R.mem_sourceAllocatedBranchSet_iff] at hvx hvy
  rcases hvx with hvxRow | ⟨e, hex, hve⟩
  · rcases hvy with hvyRow | ⟨f, hfy, hvf⟩
    · exact
        Finset.disjoint_left.mp (R.row_nodeDisjoint hxy) hvxRow hvyRow
    · exact
        Finset.disjoint_left.mp
          (R.dropLast_disjoint_row_of_source_ne f hfy hxy.symm)
          hvf hvxRow
  · rcases hvy with hvyRow | ⟨f, hfy, hvf⟩
    · exact
        Finset.disjoint_left.mp
          (R.dropLast_disjoint_row_of_source_ne e hex hxy)
          hve hvyRow
    · exact
        Finset.disjoint_left.mp
          (R.dropLast_disjoint_dropLast_of_sources_ne
            e f hex hfy hxy)
          hve hvf

/-- Every source-allocated branch set is connected: the coordinate row is the
anchor and every outgoing half-open path meets it at its source. -/
theorem sourceAllocatedBranchSet_connected
    (R : HostRealization F rows) (x : X) :
    (G.induce {v : V | v ∈ R.sourceAllocatedBranchSet x}).Connected := by
  classical
  let a := (rows x).source
  have haRow : a ∈ (rows x).vertexSet :=
    GraphPath.source_mem_vertexSet (rows x)
  have haBranch : a ∈ R.sourceAllocatedBranchSet x :=
    R.row_subset_sourceAllocatedBranchSet x haRow
  refine G.induce_connected_of_patches a haBranch ?_
  intro v hv
  change v ∈ R.sourceAllocatedBranchSet x at hv
  rw [R.mem_sourceAllocatedBranchSet_iff] at hv
  rcases hv with hvRow | ⟨e, hsource, hvDrop⟩
  · let S : Set V := {z : V | z ∈ (rows x).vertexSet}
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact R.row_subset_sourceAllocatedBranchSet x hz
    · exact haRow
    · exact hvRow
    · simpa [S] using
        (GraphPath.connected_induce_vertexSet (rows x)).preconnected
          ⟨a, haRow⟩ ⟨v, hvRow⟩
  · let Srow : Set V := {z : V | z ∈ (rows x).vertexSet}
    let Sdrop : Set V :=
      {z : V | z ∈ (R.edgePath e).dropLast.vertexSet}
    let S : Set V := Srow ∪ Sdrop
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro z hz
      change z ∈ Srow ∪ Sdrop at hz
      change z ∈ R.sourceAllocatedBranchSet x
      rw [R.mem_sourceAllocatedBranchSet_iff]
      rcases hz with hzRow | hzDrop
      · exact Or.inl (by simpa [Srow] using hzRow)
      · exact Or.inr
          ⟨e, hsource, by simpa [Sdrop] using hzDrop⟩
    · exact Or.inl (by simpa [Srow] using haRow)
    · exact Or.inr (by simpa [Sdrop] using hvDrop)
    · have hsRow :
          (R.edgePath e).source ∈ Srow := by
        simpa [Srow, hsource] using R.edgePath_source_mem e
      have hsDrop :
          (R.edgePath e).source ∈ Sdrop := by
        simpa [Sdrop] using R.edgePath_source_mem_dropLast e
      have hrowConn : (G.induce Srow).Connected := by
        simpa [Srow] using
          GraphPath.connected_induce_vertexSet (rows x)
      have hdropConn : (G.induce Sdrop).Connected := by
        simpa [Sdrop] using
          GraphPath.connected_induce_vertexSet (R.edgePath e).dropLast
      have hconn : (G.induce S).Connected := by
        simpa [S] using
          G.induce_union_connected
            hrowConn.preconnected hdropConn.preconnected
            ⟨(R.edgePath e).source, hsRow, hsDrop⟩
      exact hconn.preconnected
        ⟨a, Or.inl (by simpa [Srow] using haRow)⟩
        ⟨v, Or.inr (by simpa [Sdrop] using hvDrop)⟩

theorem edgePath_target_mem_sourceAllocatedBranchSet
    (R : HostRealization F rows) (e : F.Edge) :
    (R.edgePath e).target ∈
      R.sourceAllocatedBranchSet (F.edgeTarget e) :=
  R.row_subset_sourceAllocatedBranchSet _
    (R.edgePath_target_mem e)

theorem edgePath_penultimate_mem_sourceAllocatedBranchSet
    (R : HostRealization F rows) (e : F.Edge) :
    (R.edgePath e).penultimate ∈
      R.sourceAllocatedBranchSet (F.edgeSource e) := by
  apply R.dropLast_subset_sourceAllocatedBranchSet e
  simpa using GraphPath.target_mem_vertexSet (R.edgePath e).dropLast

/-- The canonical source allocation is a branch-set model of the simple union
of the round matchings. -/
noncomputable def toMinorModel
    (R : HostRealization F rows) :
    MinorModel F.auxiliaryGraph G where
  branchSet := R.sourceAllocatedBranchSet
  branch_nonempty := R.sourceAllocatedBranchSet_nonempty
  branch_connected := R.sourceAllocatedBranchSet_connected
  branch_disjoint := fun {_ _} hxy =>
    R.sourceAllocatedBranchSet_disjoint hxy
  adjacent := by
    intro x y hxy
    rcases hxy with ⟨e, h | h⟩
    · refine
        ⟨(R.edgePath e).penultimate, ?_,
          (R.edgePath e).target, ?_, ?_⟩
      · simpa [h.1] using
          R.edgePath_penultimate_mem_sourceAllocatedBranchSet e
      · simpa [h.2] using
          R.edgePath_target_mem_sourceAllocatedBranchSet e
      · exact R.edgePath_penultimate_adj_target e
    · refine
        ⟨(R.edgePath e).target, ?_,
          (R.edgePath e).penultimate, ?_, ?_⟩
      · simpa [h.2] using
          R.edgePath_target_mem_sourceAllocatedBranchSet e
      · simpa [h.1] using
          R.edgePath_penultimate_mem_sourceAllocatedBranchSet e
      · exact G.symm (R.edgePath_penultimate_adj_target e)

theorem isMinor_auxiliaryGraph
    (R : HostRealization F rows) :
    IsMinor F.auxiliaryGraph G :=
  ⟨R.toMinorModel⟩

end HostRealization
end RoundFamily
end CutMatchingGame
end SimpleGraph
