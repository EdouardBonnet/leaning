import «statements-and-proofs».Exponent7.CutResponder.HubObstruction

/-!
# Residual cut-responder interface

A responder for one full bisection is not by itself sufficient for peeling:
after one batch is used, the next fresh cluster must answer the bisection on
the unmatched subsets.  This module states that exact residual interface and
shows that it specializes to the Task C full-bisection statement.

No declaration here is an axiom.  The residual statement is an explicit
theorem parameter for the parallel Task D consumer.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- A clean constant-fraction response between arbitrary residual sides. -/
structure StrongClusterActiveCrossingResponse
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (responseConstant : ℕ) where
  batch :
    PrescribedBisectionRouting.CrossingCleanBatch
      (strongClusterExplicitRouting
        P i selected U W hdisjoint hcard)
  fraction :
    U.card ≤ responseConstant * batch.card

/-- Residual version of the strong-cluster cut responder.  It is the minimal
interface from which repeated fresh-cluster responses can peel a perfect
matching. -/
def StrongClusterActiveCutResponderStatement
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
          (StrongClusterActiveCrossingResponse
            P i selected U W hdisjoint hcard responseConstant)

/-- The residual responder specializes to the requested full-bisection
responder. -/
theorem strongClusterCutResponder_of_active
    {reserve responseConstant : ℕ}
    (hactive :
      StrongClusterActiveCutResponderStatement.{u}
        reserve responseConstant) :
    StrongClusterCutResponderStatement.{u}
      reserve responseConstant := by
  intro V _ _ G ell w g P i selected cut hdegree hg hwidth
  rcases hactive G P i selected cut.left cut.right
      cut.disjoint cut.card_eq hdegree hg hwidth with
    hgrid | hresponse
  · exact Or.inl hgrid
  · exact Or.inr (by
      rcases hresponse with ⟨K⟩
      refine ⟨{ batch := ?_, fraction := ?_ }⟩
      · simpa [strongClusterBisectionRouting] using K.batch
      · simpa [cutLeftLocalRows_card] using K.fraction)

/-- Residual occurrence capacity, again stated as a proposition rather than
an axiom. -/
def StrongClusterActiveOccurrenceCapacityStatement
    (reserve d : ℕ) : Prop :=
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
      PrescribedBisectionRouting.OccurrenceDegreeAtMost
        (strongClusterExplicitRouting
          P i selected U W hdisjoint hcard) d

/-- Residual occurrence capacity resolves every residual hub and supplies the
active responder with constant `2*d`. -/
theorem strongClusterActiveCutResponder_of_occurrenceCapacity
    {reserve d : ℕ}
    (hcapacity :
      StrongClusterActiveOccurrenceCapacityStatement.{u}
        reserve d) :
    StrongClusterActiveCutResponderStatement.{u}
      reserve (2 * d) := by
  intro V _ _ G ell w g P i selected U W hdisjoint hcard
      hdegree hg hwidth
  let B :=
    strongClusterExplicitRouting
      P i selected U W hdisjoint hcard
  refine Or.inr ⟨{ batch := B.maximumCrossingBatch, fraction := ?_ }⟩
  have hroute :
      B.routes.card ≤
        (2 * d) * B.maximumCrossingBatch.card :=
    B.routes_card_le_two_mul_degree_mul_maximumCrossingBatch
      (hcapacity G P i selected U W hdisjoint hcard
        hdegree hg hwidth)
  have himage :
      (U.image (localGridRow P i selected)).card = U.card := by
    rw [Finset.card_image_of_injective]
    exact (localGridRow P i selected).injective
  rw [B.routes_card, himage] at hroute
  exact hroute

end CutResponder
end Exponent7
end SimpleGraph
