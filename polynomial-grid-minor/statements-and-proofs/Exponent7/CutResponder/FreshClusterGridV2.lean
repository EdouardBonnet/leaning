import «statements-and-proofs».Exponent7.CutResponder.FreshClusterCutMatchingV2
import «statements-and-proofs».Exponent7.CutResponder.FreshClusterGrid

/-!
# Host grid minor from the existential-routing transcript

The auxiliary-minor and expander arguments are properties of the completed
transcript, so only transcript production differs from the frozen consumer.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- V2 version of the complete fresh-cluster cut-matching consumer. -/
theorem containsGridMinor_of_freshClusterCutMatchingV2
    {roundBound reserve responseConstant : ℕ}
    (hstrategy :
      ∀ responder :
          CutMatchingGame.SequentialResponder (GridVertex g),
        ∃ rounds : List
            (CutMatchingGame.LazyRound (GridVertex g)),
          rounds.length = roundBound ∧
          CutMatchingGame.IsHalfEdgeExpander rounds ∧
          CutMatchingGame.FollowsResponder responder 0 rounds)
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hroundPos : 0 < roundBound)
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    [Fintype (gridGraphULift.{0} g).edgeSet]
    (htarget :
      TargetSmallForHost
        (V := GridVertex g) (gridGraphULift.{0} g)
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor G g := by
  by_contra hnogrid
  rcases
      exists_freshClusterCutMatchingTranscriptV2
        hstrategy hclean hc hslots P selected
        hdegree hg hwidth hnogrid with
    ⟨T⟩
  have hcard : 2 ≤ Fintype.card (GridVertex g) := by
    rw [card_gridVertex]
    nlinarith
  exact hnogrid
    (T.containsGridMinor_of_expanderTheorem81
      hroundPos hcard (g' := g) htarget)

/-- Scale-separated V2 consumer. -/
theorem containsGridMinor_of_freshClusterCutMatching_scaledV2
    {q target reserve responseConstant roundBound : ℕ}
    (hstrategy :
      ∀ responder :
          CutMatchingGame.SequentialResponder (GridVertex q),
        ∃ rounds : List
            (CutMatchingGame.LazyRound (GridVertex q)),
          rounds.length = roundBound ∧
          CutMatchingGame.IsHalfEdgeExpander rounds ∧
          CutMatchingGame.FollowsResponder responder 0 rounds)
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hroundPos : 0 < roundBound)
    (hslots :
      roundBound * matchingBatchBudget responseConstant q ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex q ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (hdegree : MaxDegreeAtMost G 4)
    (hq : 2 ≤ q)
    (htarget : target ≤ q)
    (hwidth : reserve * q ^ 2 ≤ w)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hsmall :
      TargetSmallForHost
        (V := GridVertex q) (gridGraphULift.{0} target)
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor G target := by
  by_contra hnogrid
  have hnogridQ : ¬ ContainsGridMinor G q := by
    intro hqGrid
    exact hnogrid (hqGrid.of_order_le htarget)
  rcases
      exists_freshClusterCutMatchingTranscriptV2
        hstrategy hclean hc hslots P selected
        hdegree hq hwidth hnogridQ with
    ⟨T⟩
  have hcard : 2 ≤ Fintype.card (GridVertex q) := by
    rw [card_gridVertex]
    nlinarith
  exact hnogrid
    (T.containsGridMinor_of_expanderTheorem81
      hroundPos hcard (g' := target) hsmall)

end CutResponder
end Exponent7
end SimpleGraph
