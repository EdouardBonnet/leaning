import «statements-and-proofs».Exponent7.CutResponder.FractionalMatchingPeeling

/-!
# From active strong-cluster batches to an abstract perfect matching

This module converts the selected local-row endpoints in a clean response back
to their `GridVertex g` labels, proves endpoint injectivity, and feeds the
result to the finite peeling theorem.

It constructs the abstract perfect matching required by the cut-matching
game.  Path provenance across distinct fresh clusters is a separate geometric
consumer.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- Inverse of the injective image map on a selected residual row set. -/
noncomputable def localRowPreimage
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (I : Finset (GridVertex g))
    (r : {
      r : (StrongPathOfSetsSystem.clusterLinkage P i).Index //
        r ∈ I.image (localGridRow P i selected) }) :
    {x : GridVertex g // x ∈ I} :=
  ⟨Classical.choose (Finset.mem_image.mp r.2),
    (Classical.choose_spec (Finset.mem_image.mp r.2)).1⟩

theorem localRowPreimage_spec
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (I : Finset (GridVertex g))
    (r : {
      r : (StrongPathOfSetsSystem.clusterLinkage P i).Index //
        r ∈ I.image (localGridRow P i selected) }) :
    localGridRow P i selected
        (localRowPreimage P i selected I r).1 = r.1 := by
  exact
    (Classical.choose_spec (Finset.mem_image.mp r.2)).2

theorem localRowPreimage_injective
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (I : Finset (GridVertex g)) :
    Function.Injective (localRowPreimage P i selected I) := by
  intro r s hrs
  apply Subtype.ext
  rw [← localRowPreimage_spec P i selected I r,
    ← localRowPreimage_spec P i selected I s,
    congrArg Subtype.val hrs]

namespace StrongClusterActiveCrossingResponse

variable
    {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {U W : Finset (GridVertex g)}
    {hdisjoint : Disjoint U W}
    {hcard : U.card = W.card}
    {responseConstant : ℕ}

/-- Left grid label of one selected transition occurrence. -/
noncomputable def leftGrid
    (K : StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant)
    (p : {
      p : (strongClusterExplicitRouting
        P i selected U W hdisjoint hcard).routes.Index //
        p ∈ K.batch.occurrence }) :
    {x : GridVertex g // x ∈ U} :=
  localRowPreimage P i selected U
    ((strongClusterExplicitRouting
      P i selected U W hdisjoint hcard).transitionLeftRow p.1)

/-- Right grid label of one selected transition occurrence. -/
noncomputable def rightGrid
    (K : StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant)
    (p : {
      p : (strongClusterExplicitRouting
        P i selected U W hdisjoint hcard).routes.Index //
        p ∈ K.batch.occurrence }) :
    {x : GridVertex g // x ∈ W} :=
  localRowPreimage P i selected W
    ((strongClusterExplicitRouting
      P i selected U W hdisjoint hcard).transitionRightRow p.1)

theorem leftGrid_injective
    (K : StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant) :
    Function.Injective K.leftGrid := by
  classical
  let B :=
    strongClusterExplicitRouting
      P i selected U W hdisjoint hcard
  intro p q hpqGrid
  by_contra hpq
  have hroute : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hdisj :=
    K.batch.endpoint_disjoint p.2 q.2 hroute
  have hrow :
      B.transitionLeftRow p.1 =
        B.transitionLeftRow q.1 :=
    localRowPreimage_injective P i selected U hpqGrid
  have hp :
      Sum.inl (B.transitionLeftRow p.1) ∈
        B.occurrenceSupport p.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  have hq :
      Sum.inl (B.transitionLeftRow q.1) ∈
        B.occurrenceSupport q.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  exact Finset.disjoint_left.mp hdisj hp (by simpa [hrow] using hq)

theorem rightGrid_injective
    (K : StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant) :
    Function.Injective K.rightGrid := by
  classical
  let B :=
    strongClusterExplicitRouting
      P i selected U W hdisjoint hcard
  intro p q hpqGrid
  by_contra hpq
  have hroute : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hdisj :=
    K.batch.endpoint_disjoint p.2 q.2 hroute
  have hrow :
      B.transitionRightRow p.1 =
        B.transitionRightRow q.1 :=
    localRowPreimage_injective P i selected W hpqGrid
  have hp :
      Sum.inr (B.transitionRightRow p.1) ∈
        B.occurrenceSupport p.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  have hq :
      Sum.inr (B.transitionRightRow q.1) ∈
        B.occurrenceSupport q.1 := by
    simp [PrescribedBisectionRouting.occurrenceSupport]
  exact Finset.disjoint_left.mp hdisj hp (by simpa [hrow] using hq)

/-- Forget the graph paths but retain their exact endpoint pairing as one
matching subfamily. -/
noncomputable def toFractionalMatchingBatch
    (K : StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant) :
    FractionalMatchingBatch U W responseConstant where
  Edge := {
    p : (strongClusterExplicitRouting
      P i selected U W hdisjoint hcard).routes.Index //
      p ∈ K.batch.occurrence }
  left := K.leftGrid
  right := K.rightGrid
  left_injective := K.leftGrid_injective
  right_injective := K.rightGrid_injective
  fraction := by
    simpa [PrescribedBisectionRouting.CrossingCleanBatch.card] using
      K.fraction

end StrongClusterActiveCrossingResponse

/-- Away from the grid output, an active graph responder gives the pure
fractional-batch responder consumed by finite peeling. -/
theorem fractionalBatchResponder_of_strongClusterActive
    {reserve responseConstant : ℕ}
    (hactive :
      StrongClusterActiveCutResponderStatement.{u}
        reserve responseConstant)
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    FractionalBatchResponder
      (X := GridVertex g) responseConstant := by
  intro U W hdisjoint hcard hU
  rcases hactive G P i selected U W hdisjoint hcard
      hdegree hg hwidth with
    hgrid | hresponse
  · exact False.elim (hnogrid hgrid)
  · rcases hresponse with ⟨K⟩
    exact ⟨K.toFractionalMatchingBatch⟩

/-- The residual graph responder therefore produces an abstract perfect
matching across any requested bisection. -/
theorem matchingAcross_of_strongClusterActive
    {reserve responseConstant : ℕ}
    (hactive :
      StrongClusterActiveCutResponderStatement.{u}
        reserve responseConstant)
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (B : CutMatchingGame.Bisection (GridVertex g))
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    Nonempty (CutMatchingGame.MatchingAcross B) := by
  let respond :=
    fractionalBatchResponder_of_strongClusterActive
      hactive P i selected hdegree hg hwidth hnogrid
  rcases
      exists_peeledMatching_of_fractionalBatchResponder
        respond B.left B.right B.disjoint B.card_eq with
    ⟨M⟩
  exact ⟨{ toEquiv := M.toEquiv }⟩

end CutResponder
end Exponent7
end SimpleGraph
