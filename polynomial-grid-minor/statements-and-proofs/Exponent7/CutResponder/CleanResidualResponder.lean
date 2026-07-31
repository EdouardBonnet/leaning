import «statements-and-proofs».Exponent7.CutResponder.ActivePeelingBridge

/-!
# The clean residual responder needed by the minor consumer

The residual responder in `ActiveCutResponder` is enough to construct an
abstract perfect matching, but its paths are only certified clean against the
currently unmatched endpoint rows.  That is not enough for contraction:
a later batch could run internally through a selected row consumed by an
earlier batch.

This file records the exact strengthened frontier used by Task D.  Every
residual batch is internally disjoint from *all* selected global rows.  The
statement remains an explicit proposition and is not introduced as an axiom.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- Union of the complete global traces of all selected grid-coordinate
rows. -/
noncomputable def allSelectedGlobalRowVertexSet
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index) :
    Finset V :=
  (Finset.univ : Finset (GridVertex g)).biUnion fun x =>
    ((GlobalRowPrefix.globalRows P).packing.path
      (selected x)).vertexSet

theorem mem_allSelectedGlobalRowVertexSet
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (x : GridVertex g) {v : V}
    (hv :
      v ∈ ((GlobalRowPrefix.globalRows P).packing.path
        (selected x)).vertexSet) :
    v ∈ allSelectedGlobalRowVertexSet P selected := by
  classical
  rw [allSelectedGlobalRowVertexSet]
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hv⟩

/-- A residual crossing response whose paths avoid the complete selected-row
universe, including rows consumed by earlier batches. -/
structure StrongClusterCleanActiveCrossingResponse
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (responseConstant : ℕ)
    extends StrongClusterActiveCrossingResponse
      P i selected U W hdisjoint hcard responseConstant where
  internallyDisjoint_allSelected :
    ∀ p : {
      p : (strongClusterExplicitRouting
        P i selected U W hdisjoint hcard).routes.Index //
        p ∈ batch.occurrence },
      GraphPath.InternallyDisjointFromSet
        ((strongClusterExplicitRouting
          P i selected U W hdisjoint hcard).sideChangingPath p.1)
        (allSelectedGlobalRowVertexSet P selected)

/-- The precise residual theorem needed for clean fresh-cluster peeling.
This proposition is the application-specific research frontier; declaring it
does not add a logical axiom. -/
def StrongClusterCleanActiveCutResponderStatement
    (reserve responseConstant : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    {ell w g : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card),
      MaxDegreeAtMost G 4 →
      2 ≤ g →
      reserve * g ^ 2 ≤ w →
      ContainsGridMinor G g ∨
        Nonempty
          (StrongClusterCleanActiveCrossingResponse
            P i selected U W hdisjoint hcard responseConstant)

/-- Forgetting the global cleanliness field recovers the earlier residual
responder. -/
theorem strongClusterActiveCutResponder_of_cleanActive
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant) :
    StrongClusterActiveCutResponderStatement.{u}
      reserve responseConstant := by
  intro V _ _ G ell w g P i selected U W hdisjoint hcard
      hdegree hg hwidth
  rcases hclean G P i selected U W hdisjoint hcard
      hdegree hg hwidth with
    hgrid | hresponse
  · exact Or.inl hgrid
  · rcases hresponse with ⟨K⟩
    exact Or.inr ⟨K.toStrongClusterActiveCrossingResponse⟩

/-- Consequently the clean residual frontier implies the full-bisection Task
C statement. -/
theorem strongClusterCutResponder_of_cleanActive
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant) :
    StrongClusterCutResponderStatement.{u}
      reserve responseConstant :=
  strongClusterCutResponder_of_active
    (strongClusterActiveCutResponder_of_cleanActive hclean)

/-- Every selected local-row trace is contained in the complete global
selected-row universe. -/
theorem selectedLocalRowVertexSet_subset_allSelectedGlobal
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (I : Finset (GridVertex g)) :
    selectedRowVertexSet
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (I.image (localGridRow P i selected)) ⊆
      allSelectedGlobalRowVertexSet P selected := by
  classical
  intro v hv
  rw [selectedRowVertexSet] at hv
  rcases Finset.mem_biUnion.mp hv with ⟨r, hr, hvr⟩
  rcases Finset.mem_image.mp hr with ⟨x, hx, hxr⟩
  apply mem_allSelectedGlobalRowVertexSet P selected x
  exact localGridRow_path_subset_global P i selected x
    (by simpa [hxr] using hvr)

end CutResponder
end Exponent7
end SimpleGraph
