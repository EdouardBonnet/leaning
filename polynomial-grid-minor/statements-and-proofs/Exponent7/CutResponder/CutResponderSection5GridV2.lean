import «statements-and-proofs».Exponent7.RectangularSection5Assembly
import «statements-and-proofs».Exponent7.CutResponder.FixedRoundStrongSystemGridV2

/-!
# Rectangular Section 5 with the V2 cut responder

This theorem is quantitatively identical to the frozen clean-active consumer.
The amortized producer is unchanged and the final weak-system consumer now
uses an existentially selected routing in each fresh cluster.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u v

open Exponent8

namespace AmortizedSlicingDichotomy

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
    {pseudoScale h Dstar initial systemLength : ℕ}
    {cRound responseConstant reserve coordinateOrder target : ℕ}

/-- Both amortized exits feed the V2 fixed-round consumer. -/
theorem gridMinor_of_cleanActiveCutResponderV2
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
      StrongClusterCleanActiveCutResponderStatementV2.{v}
        reserve responseConstant)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve)
    (Result :
      AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        pseudoScale (32 * pseudoScale ^ 4) h Dstar initial)
    (hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hdegree : MaxDegreeAtMost H 4)
    (hpseudo : 2 ≤ pseudoScale)
    (hpseudoPow : CrossbarContract.IsPowerOfTwo pseudoScale)
    (hh : 0 < h)
    (hDstar : 0 < Dstar)
    (hSystemLength : 0 < systemLength)
    (hNlower : 64 * pseudoScale ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * pseudoScale ^ 6)
    (hproductiveBudget :
      (16 * (h + 1) * (2048 * h)) *
          (32 * Rbar.card * systemLength *
            (Nat.log 2 pseudoScale + 1)) ≤
        7 * initial)
    (hterminalBudget :
      (16 * amortizedStopThreshold h Dstar) *
          (2 * Rbar.card * systemLength) ≤
        (7 * initial) * (16 * pseudoScale ^ 4))
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
  obtain ⟨Pweak⟩ :=
    Result.weakPathOfSetsSystem
      hintersects hpseudo hpseudoPow hh hDstar hSystemLength
      hNlower hNupper hproductiveBudget hterminalBudget
  exact
    gridMinor_of_weakPathOfSetsSystem_of_fixedStrategyV2
      hstrategy hclean hcRound hc hreserve Pweak hdegree
      hcoordinate hcoordinatePow htarget hlength
      hscaledWidth hbudget

end AmortizedSlicingDichotomy

end CutResponder
end Exponent7
end SimpleGraph
