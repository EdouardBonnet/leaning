import «statements-and-proofs».Exponent7.CutResponder.FreshClusterAuxMinor
import «statements-and-proofs».HairyCrossbarGridExpander

/-!
# From a fresh-cluster transcript to a host grid minor

The geometric transcript gives a minor model of its simple auxiliary graph.
Half expansion rules out a balanced separator at scale `24 * roundBound`.
The already-formalized explicit form of Theorem 8.1 then supplies a grid minor
of the auxiliary graph, which is transported through that minor model.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g g' roundBound responseConstant : ℕ}
variable
  {hslots :
    roundBound * matchingBatchBudget responseConstant g ≤ ell}
variable {P : StrongPathOfSetsSystem G ell w}
variable
  {selected :
    GridVertex g ↪
      (GlobalRowPrefix.globalRows P).packing.Index}

namespace FreshClusterCutMatchingTranscript

/-- The auxiliary matching-union graph contains the requested grid once the
explicit target-size inequality for Theorem 8.1 holds. -/
theorem auxiliaryGraph_containsGridMinor_of_expanderTheorem81
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (hroundPos : 0 < roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    [Fintype (gridGraphULift.{0} g').edgeSet]
    (htarget :
      TargetSmallForHost
        (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor T.family.auxiliaryGraph g' := by
  exact
    containsGridMinor_of_expanderTheorem81_of_noSmallBalancedSeparator
      (H := T.family.auxiliaryGraph)
      (d := 24 * roundBound) (g := g')
      hcard
      (T.family.noSmallBalancedSeparator_auxiliaryGraph
        T.half_expander hroundPos)
      htarget

/-- Host-level fresh-cluster cut-matching consumer. -/
theorem containsGridMinor_of_expanderTheorem81
    (T : FreshClusterCutMatchingTranscript hslots P selected)
    (hroundPos : 0 < roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    [Fintype (gridGraphULift.{0} g').edgeSet]
    (htarget :
      TargetSmallForHost
        (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor G g' :=
  T.containsGridMinor_of_auxiliaryGraph
    (T.auxiliaryGraph_containsGridMinor_of_expanderTheorem81
      hroundPos hcard htarget)

end FreshClusterCutMatchingTranscript

/-- A complete parallel consumer for a supplied exact-round cut strategy.
The only graph-theoretic frontier is the clean active responder proposition;
no prescribed-matching dichotomy is assumed. -/
theorem containsGridMinor_of_freshClusterCutMatching
    {reserve responseConstant : ℕ}
    (hstrategy :
      ∀ responder :
          CutMatchingGame.SequentialResponder (GridVertex g),
        ∃ rounds : List
            (CutMatchingGame.LazyRound (GridVertex g)),
          rounds.length = roundBound ∧
          CutMatchingGame.IsHalfEdgeExpander rounds ∧
          CutMatchingGame.FollowsResponder responder 0 rounds)
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
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
      exists_freshClusterCutMatchingTranscript
        hstrategy hclean hc hslots P selected
        hdegree hg hwidth hnogrid with
    ⟨T⟩
  have hcard : 2 ≤ Fintype.card (GridVertex g) := by
    rw [card_gridVertex]
    nlinarith
  exact hnogrid
    (T.containsGridMinor_of_expanderTheorem81
      hroundPos hcard
      (g' := g) htarget)

/-- Scale-separated fresh-cluster consumer.

The cut-matching game runs on the `q^2` coordinates of `GridVertex q`, while
Theorem 8.1 is asked only for a `target x target` grid.  This separation is
essential: the explicit separator-to-grid theorem loses a polylogarithmic
factor in the host order, so its target-size budget is generally false with
`target = q`.

The hypothesis `target ≤ q` also transports the responder's early `q`-grid
exit to the requested target. -/
theorem containsGridMinor_of_freshClusterCutMatching_scaled
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
      exists_freshClusterCutMatchingTranscript
        hstrategy hclean hc hslots P selected
        hdegree hq hwidth hnogridQ with
    ⟨T⟩
  have hcard : 2 ≤ Fintype.card (GridVertex q) := by
    rw [card_gridVertex]
    nlinarith
  exact hnogrid
    (T.containsGridMinor_of_expanderTheorem81
      hroundPos hcard
      (g' := target) hsmall)

end CutResponder
end Exponent7
end SimpleGraph
