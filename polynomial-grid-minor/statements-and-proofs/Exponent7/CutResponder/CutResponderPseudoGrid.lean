import «statements-and-proofs».Exponent7.CutResponder.CutResponderAmortizedPipeline
import «statements-and-proofs».Exponent8.RootedSection42
import «statements-and-proofs».MinorTransitivity

/-!
# Pseudo-grid exit for the clean active cut responder

This is the source-facing no-crossbar branch of the parallel cut-responder
pipeline.  It runs rooted Observation 4.4, builds the initial slicing by
Theorem 4.6, executes the proved amortized Section 5 controller, and transfers
the resulting grid minor back through the contraction minor model.

The old prescribed-matching consumer remains unchanged.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

open Exponent8 Section4Reduction

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}
variable
    {pseudoScale D systemLength cRound responseConstant reserve
      coordinateOrder target : ℕ}

/-- The complete no-crossbar pseudo-grid branch for the clean active
cut-responder interface. -/
theorem gridMinor_of_pseudoGrid_noCrossbar_cleanActive
    (hstrategy :
      ∀ responder :
          CutMatchingGame.SequentialResponder
            (GridVertex coordinateOrder),
        ∃ rounds : List
            (CutMatchingGame.LazyRound
              (GridVertex coordinateOrder)),
          rounds.length =
              cutResponderRoundBound cRound coordinateOrder ∧
          CutMatchingGame.IsHalfEdgeExpander rounds ∧
          CutMatchingGame.FollowsResponder responder 0 rounds)
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve)
    (Gamma :
      PseudoGrid G A B X pseudoScale D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hpseudo : 2 ≤ pseudoScale)
    (hpseudoPow :
      CrossbarContract.IsPowerOfTwo pseudoScale)
    (hNlower :
      64 * pseudoScale ^ 4 ≤ Gamma.rowPacking.card)
    (hNupper :
      Gamma.rowPacking.card ≤ 64 * pseudoScale ^ 6)
    (hDscale : 64 * pseudoScale ^ 4 ≤ D)
    (hgood :
      exponentSevenUniformSlices pseudoScale systemLength *
            Gamma.rowPacking.card +
          (exponentSevenUniformSlices pseudoScale systemLength + 1) *
            Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty
        (Crossbar G A B X (pseudoScale ^ 2)))
    (hSystemLength : 0 < systemLength)
    (hcoordinate : 2 ≤ coordinateOrder)
    (hcoordinatePow :
      CrossbarContract.IsPowerOfTwo coordinateOrder)
    (htarget : target ≤ coordinateOrder)
    (hlength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ systemLength)
    (hscaledWidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target) :
    ContainsGridMinor G target := by
  have hNpos : 0 < Gamma.rowPacking.card := by
    have : 0 < 64 * pseudoScale ^ 4 := by positivity
    exact this.trans_le hNlower
  have hMpos :
      0 < exponentSevenUniformSlices
        pseudoScale systemLength :=
    exponentSevenUniformSlices_pos hSystemLength
  have hDpos : 0 < D := by
    have : 0 < 64 * pseudoScale ^ 4 := by positivity
    exact this.trans_le hDscale
  have hDhatPos : 0 < 32 * pseudoScale ^ 4 := by
    positivity
  have hmass :
      2 * Gamma.rowPacking.card * (4 * pseudoScale ^ 2) ≤
        (32 * pseudoScale ^ 4) *
          Gamma.rowPacking.card := by
    have hsmall :
        2 * (4 * pseudoScale ^ 2) ≤
          32 * pseudoScale ^ 4 := by
      have hpseudo2 : 1 ≤ pseudoScale ^ 2 :=
        Nat.one_le_pow 2 pseudoScale (by omega)
      nlinarith
    calc
      2 * Gamma.rowPacking.card *
            (4 * pseudoScale ^ 2) =
          Gamma.rowPacking.card *
            (2 * (4 * pseudoScale ^ 2)) := by ring
      _ ≤ Gamma.rowPacking.card *
            (32 * pseudoScale ^ 4) :=
        Nat.mul_le_mul_left Gamma.rowPacking.card hsmall
      _ = (32 * pseudoScale ^ 4) *
            Gamma.rowPacking.card := by ring
  obtain ⟨Root, hReduced, ⟨L0⟩⟩ :=
    exists_initialRecursiveSliceLayer_of_pseudoGrid
      Gamma hminimal hDpos hMpos hNpos hgood
      hDhatPos
      (by
        simpa only [
          show 2 * (32 * pseudoScale ^ 4) =
              64 * pseudoScale ^ 4 by ring]
          using hDscale)
      hmass hXdisjoint
  let H := Root.state.reducedGraph hReduced
  let Rbar := Root.state.reducedRow hReduced
  let Qbar := Root.state.reducedRetained hReduced
  have hRcard :
      Rbar.card = Gamma.rowPacking.card := by
    simp [Rbar]
  have hRlower :
      64 * pseudoScale ^ 4 ≤ Rbar.card := by
    simpa [hRcard] using hNlower
  have hRupper :
      Rbar.card ≤ 64 * pseudoScale ^ 6 := by
    simpa [hRcard] using hNupper
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar := by
    simpa [Rbar, Qbar] using
      Root.state.reducedRetained_intersects_reducedRow
        hReduced hDpos
  let C :=
    Root.recursiveSlicingContext
      hReduced hNpos hDhatPos
        (by
          simpa only [
            show 2 * (32 * pseudoScale ^ 4) =
                64 * pseudoScale ^ 4 by ring]
            using hDscale)
        hXdisjoint
  let L0' : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices
        pseudoScale systemLength)
      Rbar.card (4 * pseudoScale ^ 2)
        (32 * pseudoScale ^ 4) := by
    simpa [H, Rbar, Qbar, hRcard] using L0
  have hgrid : ContainsGridMinor H target :=
    gridMinor_of_uniformAmortizedPipeline_cleanActive
      hstrategy hclean hcRound hc hreserve C L0'
      hintersects
      (by
        simpa [H] using
          Root.state.reducedGraph_maxDegreeAtMost_four hReduced)
      hpseudo hpseudoPow hSystemLength
      hRlower hRupper hnoCrossbar
      hcoordinate hcoordinatePow htarget hlength
      hscaledWidth hbudget
  exact ContainsGridMinor.of_minor hgrid
    (by
      simpa [H] using
        Root.state.reducedGraph_isMinor hReduced)

end CutResponder
end Exponent7
end SimpleGraph
