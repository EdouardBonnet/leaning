import «statements-and-proofs».Exponent7.CutResponder.RoundFamilyHostMinor

/-!
# The fresh-cluster transcript as a host minor

This module instantiates the generic source-allocation construction for the
geometric transcript produced by `FreshClusterCutMatching`.  Paths in one
round are node-disjoint by geometric peeling.  Paths in different rounds live
in distinct strong-system clusters.  Every path is internally disjoint from
the complete selected-row universe.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g roundBound responseConstant : ℕ}
variable
  {hslots :
    roundBound * matchingBatchBudget responseConstant g ≤ ell}
variable {P : StrongPathOfSetsSystem G ell w}
variable
  {selected :
    GridVertex g ↪
      (GlobalRowPrefix.globalRows P).packing.Index}

namespace FreshClusterCutMatchingTranscript

/-- Host path corresponding to one abstract edge of the cut-matching round
family. -/
noncomputable def edgePath
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (e : T.family.Edge) : GraphPath G :=
  (T.response e.1).geometric.pathOfLeft e.2

theorem edgePath_source_mem
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (e : T.family.Edge) :
    (T.edgePath e).source ∈
      ((GlobalRowPrefix.globalRows P).packing.path
        (selected (T.family.edgeSource e))).vertexSet := by
  simpa [edgePath, CutMatchingGame.RoundFamily.edgeSource] using
    (T.response e.1).geometric.pathOfLeft_source_mem e.2

theorem edgePath_target_mem
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (e : T.family.Edge) :
    (T.edgePath e).target ∈
      ((GlobalRowPrefix.globalRows P).packing.path
        (selected (T.family.edgeTarget e))).vertexSet := by
  have h :=
    (T.response e.1).geometric.pathOfLeft_target_mem e.2
  rw [← T.matching_eq e.1] at h
  simpa [edgePath, CutMatchingGame.RoundFamily.edgeTarget] using h

theorem edgePath_internallyDisjoint_rows
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (e : T.family.Edge) :
    (T.edgePath e).InternallyDisjointFromSet
      (CutMatchingGame.RoundFamily.rowVertexSet
        (fun x : GridVertex g =>
          (GlobalRowPrefix.globalRows P).packing.path (selected x))) := by
  simpa [edgePath,
    CleanGeometricPeeledMatching.pathOfLeft,
    CutMatchingGame.RoundFamily.rowVertexSet,
    allSelectedGlobalRowVertexSet] using
      (T.response e.1).geometric.internallyDisjoint_clean
        ((T.response e.1).geometric.edgeOfLeft e.2)

/-- Paths belonging to distinct transcript edges are node-disjoint.  Same-round
paths use the peeled matching's disjointness; different rounds lie in distinct
fresh strong-system clusters. -/
theorem edgePath_nodeDisjoint
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    {e f : T.family.Edge} (hef : e ≠ f) :
    GraphPath.NodeDisjoint (T.edgePath e) (T.edgePath f) := by
  classical
  rcases e with ⟨r, x⟩
  rcases f with ⟨s, y⟩
  by_cases hrs : r = s
  · subst s
    have hxy : x ≠ y := by
      intro hxy
      apply hef
      subst y
      rfl
    simpa [edgePath] using
      (T.response r).geometric.pathOfLeft_nodeDisjoint hxy
  · let Mx := (T.response r).geometric
    let My := (T.response s).geometric
    let ex := Mx.edgeOfLeft x
    let ey := My.edgeOfLeft y
    have hslot :
        roundClusterSlot hslots r (Mx.slot ex) ≠
          roundClusterSlot hslots s (My.slot ey) :=
      roundClusterSlot_ne hslots (Or.inl hrs)
    have hregions :
        Disjoint
          (P.cluster (roundClusterSlot hslots r (Mx.slot ex)))
          (P.cluster (roundClusterSlot hslots s (My.slot ey))) :=
      P.cluster_disjoint hslot
    exact hregions.mono
      (by
        simpa [edgePath, Mx, ex] using Mx.stays ex)
      (by
        simpa [edgePath, My, ey] using My.stays ey)

/-- The exact transcript data satisfy the generic clean host-realization
interface. -/
noncomputable def toHostRealization
    (T : FreshClusterCutMatchingTranscript hslots P selected) :
    CutMatchingGame.RoundFamily.HostRealization
      T.family
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x)) where
  row_nodeDisjoint := by
    intro x y hxy
    exact
      (GlobalRowPrefix.globalRows P).packing.node_disjoint
        (fun h => hxy (selected.injective h))
  edgePath := T.edgePath
  edgePath_source_mem := T.edgePath_source_mem
  edgePath_target_mem := T.edgePath_target_mem
  edgePath_nodeDisjoint := by
    intro e f hef
    exact T.edgePath_nodeDisjoint hef
  edgePath_internallyDisjoint_rows :=
    T.edgePath_internallyDisjoint_rows

/-- The simple union of all abstract matching rounds is a minor of the strong
path-of-sets host graph. -/
theorem auxiliaryGraph_isMinor
    (T : FreshClusterCutMatchingTranscript hslots P selected) :
    IsMinor T.family.auxiliaryGraph G :=
  T.toHostRealization.isMinor_auxiliaryGraph

/-- Any grid minor found in the auxiliary graph transfers to the host graph. -/
theorem containsGridMinor_of_auxiliaryGraph
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    {g' : ℕ}
    (hgrid : ContainsGridMinor T.family.auxiliaryGraph g') :
    ContainsGridMinor G g' :=
  ContainsGridMinor.of_minor_small hgrid T.auxiliaryGraph_isMinor

end FreshClusterCutMatchingTranscript
end CutResponder
end Exponent7
end SimpleGraph
