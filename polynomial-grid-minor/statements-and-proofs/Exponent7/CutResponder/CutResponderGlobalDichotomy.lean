import «statements-and-proofs».Exponent7.CutResponder.CutResponderLocalDichotomy
import «statements-and-proofs».CutMatchingGame
import «statements-and-proofs».HairyPathOfSetsComplete

/-!
# Global propagation of the clean active cut responder

This module is parallel to `Exponent7.GlobalDichotomy`.  A hair cluster either
already yields the requested grid through the new clean active responder, or
it yields the usual local crossbar.  If every required hair cluster takes the
crossbar branch, the existing outer cut-matching-game construction finishes.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- Apply the clean active local dichotomy inside one hair-local graph. -/
theorem crossbar_or_grid_in_hairLocalGraph_cleanActive
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {ell w pseudoScale coordinateOrder target reserve
      responseConstant cRound systemLength : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (i : Fin ell)
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
    (hcutLength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ systemLength)
    (hscaledWidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target)
    (hlarge :
      exponentSevenLocalThreshold
        pseudoScale systemLength ≤ w) :
    Nonempty
        (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (pseudoScale ^ 2)) ∨
      ContainsGridMinor (Hsys.hairLocalGraph i) target := by
  rcases
      Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i
      with ⟨Pab, hPabCard, _hPabStays⟩
  rcases
      Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i
      with ⟨Pax, hPaxCard⟩
  have hleftCard : (Hsys.base.left i).card = w :=
    Hsys.base.left_card i
  have hrightCard : (Hsys.base.right i).card = w :=
    Hsys.base.right_card i
  have hyCard : (Hsys.y i).card = w :=
    Hsys.y_card i
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
  exact
    localCrossbar_or_grid_cleanActive
      (Hsys.hairLocalGraph i)
      hstrategy hclean hcRound hc hreserve
      hpseudo hpseudoPow hcoordinate hcoordinatePow
      htarget hSystemLength hcutLength hscaledWidth
      hbudget hleftCard hrightCard hyCard
      (Hsys.base.left_right_disjoint i)
      hleftY hrightY hlarge
      (fun x hx =>
        Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
      Pab hPabCard Pax.toPathPacking
      (by simpa using hPaxCard)

/-- Transport the grid alternative from a hair-local graph to the ambient
hairy-system graph. -/
theorem crossbar_or_grid_in_hairyCluster_cleanActive
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {ell w pseudoScale coordinateOrder target reserve
      responseConstant cRound systemLength : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (i : Fin ell)
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
    (hcutLength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ systemLength)
    (hscaledWidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target)
    (hlarge :
      exponentSevenLocalThreshold
        pseudoScale systemLength ≤ w) :
    Nonempty
        (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (pseudoScale ^ 2)) ∨
      ContainsGridMinor G target := by
  rcases
      crossbar_or_grid_in_hairLocalGraph_cleanActive
        Hsys i hstrategy hclean hcRound hc hreserve
        hpseudo hpseudoPow hcoordinate hcoordinatePow
        htarget hSystemLength hcutLength hscaledWidth
        hbudget hlarge
      with hcrossbar | hgrid
  · exact Or.inl hcrossbar
  · exact Or.inr (hgrid.mono (Hsys.hairLocalGraph_le i))

/-- Either all odd one-based clusters provide their local crossbar, or one
already contains the requested grid. -/
theorem local_crossbars_at_odd_clusters_or_grid_cleanActive
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {ell w pseudoScale coordinateOrder target reserve
      responseConstant cRound systemLength : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
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
    (hcutLength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ systemLength)
    (hscaledWidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target)
    (hlarge :
      exponentSevenLocalThreshold
        pseudoScale systemLength ≤ w) :
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
        crossbar_or_grid_in_hairyCluster_cleanActive
          Hsys i hstrategy hclean hcRound hc hreserve
          hpseudo hpseudoPow hcoordinate hcoordinatePow
          htarget hSystemLength hcutLength hscaledWidth
          hbudget hlarge
        with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hgrid ⟨i, hi, hminor⟩)

/-- Complete hairy-system consumer.  The local branch uses the clean active
responder; the all-crossbar branch reuses the existing outer construction. -/
theorem gridMinor_of_hairyPathOfSets_cleanActive
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
  rcases
      local_crossbars_at_odd_clusters_or_grid_cleanActive
        Hsys (hstrategy hcoordinate hcoordinatePow)
        hclean hcRound hc hreserve hpseudo hpseudoPow
        hcoordinate hcoordinatePow htarget hSystemLength
        hcutLength hscaledWidth hbudget hlocalWidth
      with hcrossbars | hgrid
  · rcases
      hcrossbarGrid G Hsys hpseudo hpseudoPow hdegree
        hlength hpseudoWidth hcrossbars
      with ⟨produced, hproduced, hminor⟩
    exact hminor.of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hpseudo htargetOuter hproduced)
  · exact hgrid

/-- Parameterized treewidth theorem for the parallel cut-responder route.
All finite scale inequalities are explicit. -/
theorem containsGridMinor_of_treewidth_parameters_cleanActive
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
      gridMinor_of_hairyPathOfSets_cleanActive
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
