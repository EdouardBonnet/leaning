import «statements-and-proofs».Exponent7.AmortizedPipeline
import «statements-and-proofs».Exponent7.CutResponder.CutResponderSection5Grid

/-!
# Uniform amortized pipeline for the cut responder

This file reuses the proved finite controller verbatim.  Only its final weak
path-of-sets consumer is replaced by the parallel fresh-cluster cut-matching
consumer.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u v

open Exponent8

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {pseudoScale systemLength : ℕ}
    {cRound responseConstant reserve coordinateOrder target : ℕ}

/-- Uniform source-facing controller with the cut-responder grid exit. -/
theorem gridMinor_of_uniformAmortizedPipeline_cleanActive
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
      StrongClusterCleanActiveCutResponderStatement.{v}
        reserve responseConstant)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve)
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar (32 * pseudoScale ^ 4))
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (exponentSevenUniformSlices pseudoScale systemLength)
      Rbar.card (4 * pseudoScale ^ 2) (32 * pseudoScale ^ 4))
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hdegree : MaxDegreeAtMost H 4)
    (hpseudo : 2 ≤ pseudoScale)
    (hpseudoPow : CrossbarContract.IsPowerOfTwo pseudoScale)
    (hSystemLength : 0 < systemLength)
    (hNlower : 64 * pseudoScale ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * pseudoScale ^ 6)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (pseudoScale ^ 2)))
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
    ContainsGridMinor H target := by
  have hNpos : 0 < Rbar.card := by
    have : 0 < 64 * pseudoScale ^ 4 := by positivity
    exact this.trans_le hNlower
  obtain ⟨Result⟩ :=
    exists_uniformAmortizedSlicingDichotomy
      C L0 hpseudo hpseudoPow hSystemLength
      hNpos hNupper hnoCrossbar
  exact
    CutResponder.AmortizedSlicingDichotomy.gridMinor_of_cleanActiveCutResponder
      hstrategy hclean hcRound hc hreserve
      Result
      hintersects hdegree hpseudo hpseudoPow
      (exponentSevenUniformDepth_pos pseudoScale)
      (exponentSevenDstar_pos (by omega))
      hSystemLength hNlower hNupper
      (exponentSeven_uniform_productive_budget
        pseudoScale Rbar.card systemLength)
      (exponentSeven_uniform_terminal_budget
        pseudoScale Rbar.card systemLength)
      hcoordinate hcoordinatePow htarget hlength
      hscaledWidth hbudget

end CutResponder
end Exponent7
end SimpleGraph
