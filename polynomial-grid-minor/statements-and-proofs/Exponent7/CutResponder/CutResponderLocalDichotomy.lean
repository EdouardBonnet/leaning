import «statements-and-proofs».Exponent7.LocalDichotomy
import «statements-and-proofs».Exponent7.CutResponder.CutResponderPseudoGrid

/-!
# Local crossbar-or-grid dichotomy for the cut responder

This parallel local theorem keeps the Theorem 4.1 and pseudo-grid scales
separate from both the cut-matching coordinate order and the requested grid
order.  The legacy conditional endpoint is imported only for its proved
arithmetic and pseudo-grid helper lemmas; it is not used as a proof input.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

open Finset Section4Reduction

universe u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Local Chuzhoy--Tan dichotomy with the clean active cut-responder
consumer in the no-crossbar branch. -/
theorem localCrossbar_or_grid_cleanActive
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V)
    {pseudoScale coordinateOrder target reserve responseConstant
      cRound systemLength kappa : ℕ}
    {A B X : Finset V}
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
    (hpseudo : 2 ≤ pseudoScale)
    (hpseudoPow :
      CrossbarContract.IsPowerOfTwo pseudoScale)
    (hcoordinate : 2 ≤ coordinateOrder)
    (hcoordinatePow :
      CrossbarContract.IsPowerOfTwo coordinateOrder)
    (htarget : target ≤ coordinateOrder)
    (hSystemLength : 0 < systemLength)
    (hlength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ systemLength)
    (hscaledWidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target)
    (hA : A.card = kappa)
    (hB : B.card = kappa)
    (hX : X.card = kappa)
    (hAB : Disjoint A B)
    (hAX : Disjoint A X)
    (hBX : Disjoint B X)
    (hlarge :
      exponentSevenLocalThreshold
        pseudoScale systemLength ≤ kappa)
    (hdegree : ∀ x ∈ X, DegreeEquals H x 1)
    (Pab : PathPacking H A B)
    (hPab : Pab.card = kappa)
    (Pax : PathPacking H A X)
    (hPax : Pax.card = kappa) :
    Nonempty
        (Crossbar H A B X (pseudoScale ^ 2)) ∨
      ContainsGridMinor H target := by
  have hdiscardCost :
      (64 * pseudoScale ^ 4) *
          (2 * pseudoScale ^ 2) ≤
        exponentSevenLocalCost
          pseudoScale systemLength := by
    have hM :
        2 ≤ exponentSevenUniformSlices
              pseudoScale systemLength + 1 := by
      have hpos :=
        exponentSevenUniformSlices_pos
          (q := pseudoScale) (ell := systemLength)
          hSystemLength
      omega
    calc
      (64 * pseudoScale ^ 4) *
            (2 * pseudoScale ^ 2) =
          2 * (64 * pseudoScale ^ 6) := by ring
      _ ≤
          (exponentSevenUniformSlices
              pseudoScale systemLength + 1) *
            (64 * pseudoScale ^ 6) :=
        Nat.mul_le_mul_right
          (64 * pseudoScale ^ 6) hM
      _ ≤
          exponentSevenLocalCost
            pseudoScale systemLength := by
        unfold exponentSevenLocalCost
        exact Nat.le_add_left _ _
  have hdepthCost :
      (64 * pseudoScale ^ 4) *
          (2 * pseudoScale ^ 2) ≤ kappa := by
    calc
      (64 * pseudoScale ^ 4) *
            (2 * pseudoScale ^ 2)
          ≤ exponentSevenLocalCost
              pseudoScale systemLength :=
        hdiscardCost
      _ ≤
          8 * exponentSevenLocalCost
            pseudoScale systemLength := by omega
      _ =
          exponentSevenLocalThreshold
            pseudoScale systemLength := rfl
      _ ≤ kappa := hlarge
  have hDle :
      64 * pseudoScale ^ 4 ≤
        kappa / (2 * pseudoScale ^ 2) := by
    apply
      (Nat.le_div_iff_mul_le
        (by positivity :
          0 < 2 * pseudoScale ^ 2)).2
    exact hdepthCost
  rcases
      theorem_four_one_of_pathPackings
        H hpseudo hpseudoPow hA hB hX hAB hAX hBX
        hdegree Pab hPab Pax hPax
        (Nat.succ_le_of_lt (by positivity))
        hDle with
    ⟨P, Q, hPcard, hQcard, hminimal, hconclusion⟩
  rcases hconclusion with hcross | hpseudoGrid
  · exact Or.inl hcross
  · by_cases hcross :
        Nonempty
          (Crossbar H A B X (pseudoScale ^ 2))
    · exact Or.inl hcross
    · rcases hpseudoGrid with ⟨Gamma⟩
      have hXdisjoint :
          ∀ p : P.Index,
            Disjoint X (P.path p).vertexSet := by
        let Setup : Theorem41Setup
            H A B X pseudoScale kappa
              (64 * pseudoScale ^ 4) P Q :=
          { two_le_g := hpseudo
            g_power_two := hpseudoPow
            A_card := hA
            B_card := hB
            X_card := hX
            disjoint_A_B := hAB
            disjoint_A_X := hAX
            disjoint_B_X := hBX
            degree_X := hdegree
            P_card := hPcard
            Q_card := hQcard
            minimal_pair := hminimal
            D_pos := by
              have :
                  0 < 64 * pseudoScale ^ 4 := by
                positivity
              omega
            D_le := hDle }
        intro p
        exact (Setup.P_path_disjoint_X p).symm
      have hgood :
          exponentSevenUniformSlices
                pseudoScale systemLength *
                Gamma.rowPacking.card +
              (exponentSevenUniformSlices
                  pseudoScale systemLength + 1) *
                Gamma.rowPacking.card ≤
            Gamma.goodQSet.card :=
        SimpleGraph.Exponent7.PseudoGrid.uniform_slicing_budget
          Gamma hSystemLength hlarge hPcard
      have hgoodNonempty : Gamma.goodQSet.Nonempty :=
        SimpleGraph.Exponent7.PseudoGrid.goodQSet_nonempty_of_uniformThreshold
          Gamma hpseudo hSystemLength hlarge hPcard
      have hrowBounds :
          64 * pseudoScale ^ 4 ≤
              Gamma.rowPacking.card ∧
            Gamma.rowPacking.card ≤
              64 * pseudoScale ^ 6 := by
        have h :=
          Gamma.rowPacking_card_bounds_of_goodQSet_nonempty
            hgoodNonempty
        constructor
        · exact h.1
        · simpa only [
            show
              (64 * pseudoScale ^ 4) *
                  pseudoScale ^ 2 =
                64 * pseudoScale ^ 6 by ring]
            using h.2
      have hgrid : ContainsGridMinor H target :=
        gridMinor_of_pseudoGrid_noCrossbar_cleanActive
          (pseudoScale := pseudoScale)
          (D := 64 * pseudoScale ^ 4)
          (systemLength := systemLength)
          (cRound := cRound)
          (responseConstant := responseConstant)
          (reserve := reserve)
          (coordinateOrder := coordinateOrder)
          (target := target)
          hstrategy hclean hcRound hc hreserve
          Gamma hminimal hpseudo hpseudoPow
          hrowBounds.1 hrowBounds.2 le_rfl hgood
          hXdisjoint hcross hSystemLength
          hcoordinate hcoordinatePow htarget hlength
          hscaledWidth hbudget
      exact Or.inr hgrid

end CutResponder
end Exponent7
end SimpleGraph
