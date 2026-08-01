import «statements-and-proofs».Exponent7.CutResponder.CleanResidualResponderV2
import «statements-and-proofs».Exponent7.CutResponder.FreshStrongClusterMatching

/-!
# Fresh-cluster matching from an existentially chosen routing

This is the V2 adapter from a clean response carrying its own routing to the
generic geometric peeling theorem.  The peeling construction itself is
unchanged; only the dependent source of each transition path is different.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

namespace StrongClusterCleanActiveCrossingResponseFor

variable
    {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {U W : Finset (GridVertex g)}
    {hdisjoint : Disjoint U W}
    {hcard : U.card = W.card}
    {routing :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)}
    {responseConstant : ℕ}

/-- Original grid label of the left transition row. -/
noncomputable def leftGrid
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant)
    (p : {p : routing.routes.Index // p ∈ K.batch.occurrence}) :
    {x : GridVertex g // x ∈ U} :=
  localRowPreimage P i selected U (routing.transitionLeftRow p.1)

/-- Original grid label of the right transition row. -/
noncomputable def rightGrid
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant)
    (p : {p : routing.routes.Index // p ∈ K.batch.occurrence}) :
    {x : GridVertex g // x ∈ W} :=
  localRowPreimage P i selected W (routing.transitionRightRow p.1)

theorem leftGrid_injective
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant) :
    Function.Injective K.leftGrid := by
  classical
  intro p q hpqGrid
  by_contra hpq
  have hroute : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hdisj :=
    K.batch.endpoint_disjoint p.2 q.2 hroute
  have hrow :
      routing.transitionLeftRow p.1 =
        routing.transitionLeftRow q.1 :=
    localRowPreimage_injective P i selected U hpqGrid
  have hp :
      Sum.inl (routing.transitionLeftRow p.1) ∈
        routing.occurrenceSupport p.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  have hq :
      Sum.inl (routing.transitionLeftRow q.1) ∈
        routing.occurrenceSupport q.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  exact Finset.disjoint_left.mp hdisj hp (by simpa [hrow] using hq)

theorem rightGrid_injective
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant) :
    Function.Injective K.rightGrid := by
  classical
  intro p q hpqGrid
  by_contra hpq
  have hroute : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hdisj :=
    K.batch.endpoint_disjoint p.2 q.2 hroute
  have hrow :
      routing.transitionRightRow p.1 =
        routing.transitionRightRow q.1 :=
    localRowPreimage_injective P i selected W hpqGrid
  have hp :
      Sum.inr (routing.transitionRightRow p.1) ∈
        routing.occurrenceSupport p.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  have hq :
      Sum.inr (routing.transitionRightRow q.1) ∈
        routing.occurrenceSupport q.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  exact Finset.disjoint_left.mp hdisj hp (by simpa [hrow] using hq)

/-- Forget path geometry while retaining the endpoint pairing selected by the
stored routing. -/
noncomputable def toFractionalMatchingBatch
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant) :
    FractionalMatchingBatch U W responseConstant where
  Edge := {p : routing.routes.Index // p ∈ K.batch.occurrence}
  left := K.leftGrid
  right := K.rightGrid
  left_injective := K.leftGrid_injective
  right_injective := K.rightGrid_injective
  fraction := by
    simpa [PrescribedBisectionRouting.CrossingCleanBatch.card] using
      K.fraction

/-- Interpret a V2 response as one generic geometric batch on the selected
global rows. -/
noncomputable def toCleanGeometricFractionalBatch
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard routing responseConstant) :
    CleanGeometricFractionalBatch
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (P.cluster i)
      U W responseConstant := by
  classical
  let M := K.toFractionalMatchingBatch
  refine
    { matching := M
      path := fun p => routing.sideChangingPath p.1
      source_mem_row := ?_
      target_mem_row := ?_
      stays := ?_
      node_disjoint := ?_
      internallyDisjoint_clean := ?_ }
  · intro p
    have hlocal :=
      routing.sideChangingPath_source_mem_transitionLeftRow p.1
    have hindex :
        localGridRow P i selected (K.leftGrid p).1 =
          (routing.transitionLeftRow p.1).1 :=
      localRowPreimage_spec P i selected U
        (routing.transitionLeftRow p.1)
    have hglobal :=
      localGridRow_path_subset_global
        P i selected (K.leftGrid p).1
        (by simpa [hindex] using hlocal)
    simpa [M, toFractionalMatchingBatch] using hglobal
  · intro p
    have hlocal :=
      routing.sideChangingPath_target_mem_transitionRightRow p.1
    have hindex :
        localGridRow P i selected (K.rightGrid p).1 =
          (routing.transitionRightRow p.1).1 :=
      localRowPreimage_spec P i selected W
        (routing.transitionRightRow p.1)
    have hglobal :=
      localGridRow_path_subset_global
        P i selected (K.rightGrid p).1
        (by simpa [hindex] using hlocal)
    simpa [M, toFractionalMatchingBatch] using hglobal
  · intro p
    exact routing.sideChangingPath_stays p.1
  · intro p q hpq
    exact K.batch.path_nodeDisjoint hpq
  · intro p
    exact K.internallyDisjoint_allSelected p

end StrongClusterCleanActiveCrossingResponseFor

/-- Away from the grid outcome, V2 supplies the same finite geometric
responder used by the existing peeling theorem. -/
theorem finiteCleanGeometricResponder_of_strongClusterCleanActiveV2
    {reserve responseConstant budget : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
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
    exact ⟨K.toResponseFor.toCleanGeometricFractionalBatch⟩

/-- One requested bisection is peeled into a clean perfect matching from V2
responses in fresh clusters. -/
theorem exists_freshStrongClusterMatchingV2
    {reserve responseConstant budget : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
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
    finiteCleanGeometricResponder_of_strongClusterCleanActiveV2
      hclean P selected slot hdegree hg hwidth hnogrid
  exact exists_cleanGeometricPeeledMatching
    respond
    (selectedClusterRegions_pairwiseDisjoint P slot)
    hc B.left B.right B.disjoint B.card_eq hbudget

end CutResponder
end Exponent7
end SimpleGraph
