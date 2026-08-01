import «statements-and-proofs».Exponent7.CutResponder.CleanResidualResponder

/-!
# Existential-routing clean residual responders

The first clean residual responder was phrased using
`strongClusterExplicitRouting`, a particular linkage selected by
`Classical.choose`.  This module records the source-faithful interface: the
response carries the routing whose side-changing transitions it uses.

The original responder implies this version by storing its canonical routing.
The converse is intentionally neither stated nor needed.  In particular, a
future proof may choose a routing which minimizes its intersections with the
selected global rows.

No declaration in this module is an axiom.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- A clean response for one explicitly supplied routing.  This auxiliary
structure is convenient for the finite-descent argument: it lets us ask
whether a fixed candidate routing already gives the desired response. -/
structure StrongClusterCleanActiveCrossingResponseFor
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (routing :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i))
    (responseConstant : ℕ) where
  batch : PrescribedBisectionRouting.CrossingCleanBatch routing
  fraction : U.card ≤ responseConstant * batch.card
  internallyDisjoint_allSelected :
    ∀ p : {p : routing.routes.Index // p ∈ batch.occurrence},
      (routing.sideChangingPath p.1).InternallyDisjointFromSet
        (allSelectedGlobalRowVertexSet P selected)

/-- A residual clean response which existentially chooses its routing rather
than demanding a property of the canonical `Classical.choose` witness. -/
structure StrongClusterCleanActiveCrossingResponseV2
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (responseConstant : ℕ) where
  routing :
    PrescribedBisectionRouting
      (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
      (fun r =>
        ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
      (U.image (localGridRow P i selected))
      (W.image (localGridRow P i selected))
      (P.cluster i)
  batch : PrescribedBisectionRouting.CrossingCleanBatch routing
  fraction : U.card ≤ responseConstant * batch.card
  internallyDisjoint_allSelected :
    ∀ p : {p : routing.routes.Index // p ∈ batch.occurrence},
      (routing.sideChangingPath p.1).InternallyDisjointFromSet
        (allSelectedGlobalRowVertexSet P selected)

namespace StrongClusterCleanActiveCrossingResponseV2

variable
    {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {U W : Finset (GridVertex g)}
    {hdisjoint : Disjoint U W}
    {hcard : U.card = W.card}
    {responseConstant : ℕ}

/-- Forget the existential packaging while keeping the selected routing
fixed. -/
def toResponseFor
    (K : StrongClusterCleanActiveCrossingResponseV2
      P i selected U W hdisjoint hcard responseConstant) :
    StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard K.routing responseConstant where
  batch := K.batch
  fraction := K.fraction
  internallyDisjoint_allSelected := K.internallyDisjoint_allSelected

end StrongClusterCleanActiveCrossingResponseV2

/-- The existential-routing residual frontier. -/
def StrongClusterCleanActiveCutResponderStatementV2
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
          (StrongClusterCleanActiveCrossingResponseV2
            P i selected U W hdisjoint hcard responseConstant)

/-- The older, choice-bound responder is strictly stronger than the
existential-routing interface. -/
theorem strongClusterCleanActiveCutResponderV2_of_v1
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant) :
    StrongClusterCleanActiveCutResponderStatementV2.{u}
      reserve responseConstant := by
  intro V _ _ G ell w g P i selected U W hdisjoint hcard
      hdegree hg hwidth
  rcases hclean G P i selected U W hdisjoint hcard
      hdegree hg hwidth with
    hgrid | hresponse
  · exact Or.inl hgrid
  · rcases hresponse with ⟨K⟩
    exact Or.inr ⟨{
      routing :=
        strongClusterExplicitRouting
          P i selected U W hdisjoint hcard
      batch := K.batch
      fraction := K.fraction
      internallyDisjoint_allSelected :=
        K.internallyDisjoint_allSelected }⟩

end CutResponder
end Exponent7
end SimpleGraph
