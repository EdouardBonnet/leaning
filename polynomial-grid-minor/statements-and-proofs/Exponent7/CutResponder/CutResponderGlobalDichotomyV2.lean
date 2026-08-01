import «statements-and-proofs».Exponent7.CutResponder.CutResponderGlobalDichotomy
import «statements-and-proofs».Exponent7.CutResponder.CutResponderLocalDichotomyV2

/-!
# Global propagation of the existential clean active responder

The outer hairy-system argument is insensitive to which routing witnesses a
local response.  This module repeats only that propagation for the corrected
V2 responder and reuses the existing crossbar assembly verbatim.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- Complete hairy-system consumer for the routing-existential V2 responder. -/
theorem gridMinor_of_hairyPathOfSets_cleanActiveV2
    {reserve responseConstant cRound : ℕ}
    (hstrategy :
      ∀ {coordinateOrder : ℕ},
        2 ≤ coordinateOrder →
        CrossbarContract.IsPowerOfTwo coordinateOrder →
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
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant) :
    ∃ cGrid : ℕ, 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V)
        {ell w pseudoScale coordinateOrder target
          systemLength : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          0 < cRound →
          0 < responseConstant →
          0 < reserve →
          2 ≤ pseudoScale →
          CrossbarContract.IsPowerOfTwo pseudoScale →
          2 ≤ coordinateOrder →
          CrossbarContract.IsPowerOfTwo coordinateOrder →
          target ≤ coordinateOrder →
          0 < systemLength →
          cutResponderStrongLength
              cRound responseConstant coordinateOrder ≤
            systemLength →
          20000 * (reserve * coordinateOrder ^ 2) ≤
            pseudoScale ^ 2 →
          CutResponderTargetBudget
            cRound coordinateOrder target →
          MaxDegreeAtMost G 3 →
          cGrid * Nat.log 2 pseudoScale ≤ ell →
          pseudoScale ^ 2 ≤ w →
          exponentSevenLocalThreshold
              pseudoScale systemLength ≤ w →
          cGrid * target *
              (Nat.log 2 pseudoScale) ^ 2 ≤ pseudoScale →
          [Fintype (gridGraphULift.{0} target).edgeSet] →
          ContainsGridMinor G target := by
  rcases
      HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame
      with ⟨cGrid, hcGrid, hcrossbarGrid⟩
  refine ⟨cGrid, hcGrid, ?_⟩
  intro V _ _ G ell w pseudoScale coordinateOrder target
    systemLength Hsys hcRound hc hreserve hpseudo
    hpseudoPow hcoordinate hcoordinatePow htarget
    hSystemLength hcutLength hscaledWidth hbudget
    hdegree hlength hpseudoWidth hlocalWidth
    htargetOuter instEdges
  have hlocal :
      (∀ i : Fin ell,
          HairyCrossbarGrid.OneBasedOdd i →
          Nonempty
            (Crossbar (Hsys.hairLocalGraph i)
              (Hsys.base.left i) (Hsys.base.right i)
              (Hsys.y i) (pseudoScale ^ 2))) ∨
        ContainsGridMinor G target := by
    by_cases hgrid :
        ∃ i : Fin ell,
          HairyCrossbarGrid.OneBasedOdd i ∧
            ContainsGridMinor G target
    · rcases hgrid with ⟨_i, _hi, hminor⟩
      exact Or.inr hminor
    · refine Or.inl ?_
      intro i hi
      rcases
          Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i
          with ⟨Pab, hPabCard, _hPabStays⟩
      rcases
          Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i
          with ⟨Pax, hPaxCard⟩
      have hleftY :
          Disjoint (Hsys.base.left i) (Hsys.y i) := by
        rw [Finset.disjoint_left]
        intro v hvLeft hvY
        exact Finset.disjoint_left.mp
          (Hsys.hairCluster_disjoint_base i i)
          (Hsys.y_subset_hairCluster i hvY)
          (Hsys.base.left_subset_cluster i hvLeft)
      have hrightY :
          Disjoint (Hsys.base.right i) (Hsys.y i) := by
        rw [Finset.disjoint_left]
        intro v hvRight hvY
        exact Finset.disjoint_left.mp
          (Hsys.hairCluster_disjoint_base i i)
          (Hsys.y_subset_hairCluster i hvY)
          (Hsys.base.right_subset_cluster i hvRight)
      rcases
          localCrossbar_or_grid_cleanActiveV2
            (Hsys.hairLocalGraph i)
            (hstrategy hcoordinate hcoordinatePow)
            hclean hcRound hc hreserve
            hpseudo hpseudoPow hcoordinate hcoordinatePow
            htarget hSystemLength hcutLength hscaledWidth
            hbudget
            (Hsys.base.left_card i)
            (Hsys.base.right_card i)
            (Hsys.y_card i)
            (Hsys.base.left_right_disjoint i)
            hleftY hrightY hlocalWidth
            (fun x hx =>
              Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
            Pab hPabCard Pax.toPathPacking
            (by simpa using hPaxCard)
          with hcrossbar | hminor
      · exact hcrossbar
      · exact False.elim
          (hgrid ⟨i, hi, hminor.mono (Hsys.hairLocalGraph_le i)⟩)
  rcases hlocal with hcrossbars | hgrid
  · rcases
      hcrossbarGrid G Hsys hpseudo hpseudoPow hdegree
        hlength hpseudoWidth hcrossbars
      with ⟨produced, hproduced, hminor⟩
    exact hminor.of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hpseudo htargetOuter hproduced)
  · exact hgrid

/-- Parameterized treewidth theorem for the routing-existential responder.
All finite scale inequalities are identical to the V1 theorem. -/
theorem containsGridMinor_of_treewidth_parameters_cleanActiveV2
    {reserve responseConstant cRound : ℕ}
    (hstrategy :
      ∀ {coordinateOrder : ℕ},
        2 ≤ coordinateOrder →
        CrossbarContract.IsPowerOfTwo coordinateOrder →
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
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant) :
    ∃ cHair cHairLog cGrid : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V)
        {ell w k pseudoScale coordinateOrder target
          systemLength : ℕ},
          1 < ell →
          1 < w →
          1 < k →
          k ≤ treewidth G →
          cHair * w * ell ^ 50 *
              (Nat.log 2 k) ^ cHairLog < k →
          0 < cRound →
          0 < responseConstant →
          0 < reserve →
          2 ≤ pseudoScale →
          CrossbarContract.IsPowerOfTwo pseudoScale →
          2 ≤ coordinateOrder →
          CrossbarContract.IsPowerOfTwo coordinateOrder →
          target ≤ coordinateOrder →
          0 < systemLength →
          cutResponderStrongLength
              cRound responseConstant coordinateOrder ≤
            systemLength →
          20000 * (reserve * coordinateOrder ^ 2) ≤
            pseudoScale ^ 2 →
          CutResponderTargetBudget
            cRound coordinateOrder target →
          cGrid * Nat.log 2 pseudoScale ≤ ell →
          pseudoScale ^ 2 ≤ w →
          exponentSevenLocalThreshold
              pseudoScale systemLength ≤ w →
          cGrid * target *
              (Nat.log 2 pseudoScale) ^ 2 ≤ pseudoScale →
          [Fintype (gridGraphULift.{0} target).edgeSet] →
          ContainsGridMinor G target := by
  rcases
      PolynomialGridMinor.exists_hairyPathOfSetsInput_proved
      with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases
      gridMinor_of_hairyPathOfSets_cleanActiveV2
        hstrategy hclean
      with ⟨cGrid, hcGrid, hmain⟩
  refine
    ⟨cHair, cHairLog, cGrid,
      hcHair, hcHairLog, hcGrid, ?_⟩
  intro V _ _ G ell w k pseudoScale coordinateOrder
    target systemLength hell hw hk htw hhairyLarge
    hcRound hc hreserve hpseudo hpseudoPow hcoordinate
    hcoordinatePow htarget hSystemLength hcutLength
    hscaledWidth hbudget hlength hpseudoWidth
    hlocalWidth htargetOuter instEdges
  rcases
      hhairy G hell hw hk htw hhairyLarge
      with ⟨H, hHG, hdegree, ⟨Hsys⟩⟩
  exact
    (hmain H Hsys hcRound hc hreserve hpseudo
      hpseudoPow hcoordinate hcoordinatePow htarget
      hSystemLength hcutLength hscaledWidth hbudget
      hdegree hlength hpseudoWidth hlocalWidth
      htargetOuter).mono hHG

end CutResponder
end Exponent7
end SimpleGraph
