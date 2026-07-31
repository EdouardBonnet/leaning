import «statements-and-proofs».Exponent7.CutResponder.FreshClusterPeeling

/-!
# One clean perfect matching realized in fresh strong clusters

This file instantiates the generic finite-slot peeling theorem with pairwise
disjoint clusters of a strong path-of-sets system.  The output retains:

* the exact perfect matching across the requested bisection;
* one concrete host path for every matching edge;
* pairwise node-disjointness of those paths;
* internal disjointness from every selected global row; and
* the fresh cluster slot used by every path.

The only mathematical frontier is the explicitly supplied
`StrongClusterCleanActiveCutResponderStatement`; no axiom is declared.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

namespace StrongClusterCleanActiveCrossingResponse

variable
    {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {U W : Finset (GridVertex g)}
    {hdisjoint : Disjoint U W}
    {hcard : U.card = W.card}
    {responseConstant : ℕ}

/-- Interpret a clean active response as one generic geometric batch on the
selected global rows. -/
noncomputable def toCleanGeometricFractionalBatch
    (K : StrongClusterCleanActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant) :
    CleanGeometricFractionalBatch
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (P.cluster i)
      U W responseConstant := by
  classical
  let A := K.toStrongClusterActiveCrossingResponse
  let B :=
    strongClusterExplicitRouting
      P i selected U W hdisjoint hcard
  let M := A.toFractionalMatchingBatch
  refine
    { matching := M
      path := fun p => B.sideChangingPath p.1
      source_mem_row := ?_
      target_mem_row := ?_
      stays := ?_
      node_disjoint := ?_
      internallyDisjoint_clean := ?_ }
  · intro p
    have hlocal :=
      B.sideChangingPath_source_mem_transitionLeftRow p.1
    have hindex :
        localGridRow P i selected (A.leftGrid p).1 =
          (B.transitionLeftRow p.1).1 :=
      localRowPreimage_spec P i selected U
        (B.transitionLeftRow p.1)
    have hglobal :=
      localGridRow_path_subset_global
        P i selected (A.leftGrid p).1
        (by simpa [hindex] using hlocal)
    simpa [M,
      StrongClusterActiveCrossingResponse.toFractionalMatchingBatch]
      using hglobal
  · intro p
    have hlocal :=
      B.sideChangingPath_target_mem_transitionRightRow p.1
    have hindex :
        localGridRow P i selected (A.rightGrid p).1 =
          (B.transitionRightRow p.1).1 :=
      localRowPreimage_spec P i selected W
        (B.transitionRightRow p.1)
    have hglobal :=
      localGridRow_path_subset_global
        P i selected (A.rightGrid p).1
        (by simpa [hindex] using hlocal)
    simpa [M,
      StrongClusterActiveCrossingResponse.toFractionalMatchingBatch]
      using hglobal
  · intro p
    exact B.sideChangingPath_stays p.1
  · intro p q hpq
    exact A.batch.path_nodeDisjoint hpq
  · intro p
    exact K.internallyDisjoint_allSelected p

end StrongClusterCleanActiveCrossingResponse

/-- Selected fresh strong clusters are pairwise vertex-disjoint. -/
theorem selectedClusterRegions_pairwiseDisjoint
    (P : StrongPathOfSetsSystem G ell w)
    {budget : ℕ} (slot : Fin budget ↪ Fin ell) :
    Pairwise fun s t : Fin budget =>
      Disjoint (P.cluster (slot s)) (P.cluster (slot t)) := by
  intro s t hst
  apply P.cluster_disjoint
  intro heq
  exact hst (slot.injective heq)

/-- Away from the grid outcome, the clean active frontier supplies the finite
geometric responder on any injected family of fresh clusters. -/
theorem finiteCleanGeometricResponder_of_strongClusterCleanActive
    {reserve responseConstant budget : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (slot : Fin budget ↪ Fin ell)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    FiniteCleanGeometricBatchResponder
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      responseConstant := by
  intro t U W hdisjoint hcard hU
  rcases hclean G P (slot t) selected U W hdisjoint hcard
      hdegree hg hwidth with
    hgrid | hresponse
  · exact False.elim (hnogrid hgrid)
  · rcases hresponse with ⟨K⟩
    exact ⟨K.toCleanGeometricFractionalBatch⟩

/-- One bisection is peeled into a clean perfect matching using at most the
explicit logarithmic number of fresh cluster slots. -/
theorem exists_freshStrongClusterMatching
    {reserve responseConstant budget : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (slot : Fin budget ↪ Fin ell)
    (B : CutMatchingGame.Bisection (GridVertex g))
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g)
    (hbudget :
      responseConstant *
          (Nat.log 2 B.left.card + 1) ≤ budget) :
    ∃ M : CleanGeometricPeeledMatching
        (fun x : GridVertex g =>
          (GlobalRowPrefix.globalRows P).packing.path (selected x))
        (allSelectedGlobalRowVertexSet P selected)
        (fun t => P.cluster (slot t))
        B.left B.right responseConstant 0,
      M.matching.batchCount ≤
        responseConstant * (Nat.log 2 B.left.card + 1) := by
  let respond :=
    finiteCleanGeometricResponder_of_strongClusterCleanActive
      hclean P selected slot hdegree hg hwidth hnogrid
  exact exists_cleanGeometricPeeledMatching
    respond
    (selectedClusterRegions_pairwiseDisjoint P slot)
    hc B.left B.right B.disjoint B.card_eq hbudget

/-- Forgetting the geometry gives the exact matching move consumed by the
abstract cut-matching strategy. -/
noncomputable def
    CleanGeometricPeeledMatching.toMatchingAcross
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0) :
    CutMatchingGame.MatchingAcross B where
  toEquiv := M.matching.toPeeledMatching.toEquiv

namespace CleanGeometricPeeledMatching

/-- The edge carried by a prescribed left endpoint of the exact peeled
matching.  This is the indexing bridge from the geometric peeling output to
the cut-matching game's left-endpoint representation of matching edges. -/
noncomputable def edgeOfLeft
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    M.matching.Edge :=
  (Equiv.ofBijective M.matching.left
    M.matching.left_bijective).symm x

@[simp]
theorem left_edgeOfLeft
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    M.matching.left (M.edgeOfLeft x) = x := by
  exact
    (Equiv.ofBijective M.matching.left
      M.matching.left_bijective).apply_symm_apply x

@[simp]
theorem right_edgeOfLeft
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    M.matching.right (M.edgeOfLeft x) =
      (M.toMatchingAcross.toEquiv x) := by
  simp [toMatchingAcross, PeeledMatching.toEquiv, edgeOfLeft]

/-- Concrete path indexed in the same way as a cut-matching edge. -/
noncomputable def pathOfLeft
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    GraphPath G :=
  M.path (M.edgeOfLeft x)

theorem pathOfLeft_source_mem
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    (M.pathOfLeft x).source ∈
      ((GlobalRowPrefix.globalRows P).packing.path
        (selected x.1)).vertexSet := by
  simpa [pathOfLeft] using M.source_mem_row (M.edgeOfLeft x)

theorem pathOfLeft_target_mem
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    (x : {x : GridVertex g // x ∈ B.left}) :
    (M.pathOfLeft x).target ∈
      ((GlobalRowPrefix.globalRows P).packing.path
        (selected ((M.toMatchingAcross).rightEndpoint x))).vertexSet := by
  have h :=
    M.target_mem_row (M.edgeOfLeft x)
  simpa [pathOfLeft, CutMatchingGame.MatchingAcross.rightEndpoint]
    using h

theorem pathOfLeft_nodeDisjoint
    {budget responseConstant : ℕ}
    {P : StrongPathOfSetsSystem G ell w}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {slot : Fin budget ↪ Fin ell}
    {B : CutMatchingGame.Bisection (GridVertex g)}
    (M : CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t => P.cluster (slot t))
      B.left B.right responseConstant 0)
    {x y : {x : GridVertex g // x ∈ B.left}} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint (M.pathOfLeft x) (M.pathOfLeft y) := by
  apply M.node_disjoint
  intro heq
  apply hxy
  rw [← M.left_edgeOfLeft x, ← M.left_edgeOfLeft y, heq]

end CleanGeometricPeeledMatching

end CutResponder
end Exponent7
end SimpleGraph
