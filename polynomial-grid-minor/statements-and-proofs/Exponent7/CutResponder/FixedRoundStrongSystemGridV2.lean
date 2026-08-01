import «statements-and-proofs».Exponent7.CutResponder.FreshClusterGridV2
import «statements-and-proofs».Exponent7.CutResponder.FixedRoundStrongSystemGrid

/-!
# Fixed-round strong-system consumer for the V2 responder

All constants and arithmetic predicates are reused unchanged from the frozen
consumer.  Only the responder hypothesis is replaced by the
existential-routing V2 statement.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- A supplied exact-round strategy turns a sufficiently long and wide strong
path-of-sets system into the requested grid using V2 responses. -/
theorem gridMinor_of_strongPathOfSetsSystem_of_fixedStrategyV2
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {ell w cRound responseConstant reserve coordinateOrder target : ℕ}
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
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve)
    (P : StrongPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4)
    (hq : 2 ≤ coordinateOrder)
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder)
    (htarget : target ≤ coordinateOrder)
    (hlength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ ell)
    (hwidth : reserve * coordinateOrder ^ 2 ≤ w)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target) :
    ContainsGridMinor G target := by
  let selected :
      GridVertex coordinateOrder ↪
        (GlobalRowPrefix.globalRows P).packing.Index :=
    let selectedFin :=
      (GlobalRowPrefix.globalRows P).selectedGlobalIndex
        (coordinateOrder ^ 2) (by
          have hr : 1 ≤ reserve := Nat.succ_le_iff.mpr hreserve
          calc
            coordinateOrder ^ 2 = 1 * coordinateOrder ^ 2 := by simp
            _ ≤ reserve * coordinateOrder ^ 2 :=
              Nat.mul_le_mul_right _ hr
            _ ≤ w := hwidth)
    { toFun := fun x =>
        selectedFin
          (HairyCrossbarGrid.gridVertexEquivFin coordinateOrder x)
      inj' :=
        selectedFin.injective.comp
          (HairyCrossbarGrid.gridVertexEquivFin
            coordinateOrder).injective }
  apply containsGridMinor_of_freshClusterCutMatching_scaledV2
    (q := coordinateOrder) (target := target)
    hstrategy hclean hc
    (cutResponderRoundBound_pos hcRound hq)
    hlength P selected hdegree hq htarget hwidth
  exact
    targetSmallForHost_of_cutResponderTargetBudget
      hpow hbudget

/-- The repository's exact adversarial strategy supplies the V2 strong-system
consumer with exactly the same constants. -/
theorem exists_roundConstant_gridMinor_of_strongPathOfSetsSystemV2
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V}
        {ell w coordinateOrder target : ℕ}
        [Fintype (gridGraphULift.{0} target).edgeSet]
        (P : StrongPathOfSetsSystem G ell w),
          MaxDegreeAtMost G 4 →
          2 ≤ coordinateOrder →
          CrossbarContract.IsPowerOfTwo coordinateOrder →
          target ≤ coordinateOrder →
          cutResponderStrongLength
              cRound responseConstant coordinateOrder ≤ ell →
          reserve * coordinateOrder ^ 2 ≤ w →
          CutResponderTargetBudget
              cRound coordinateOrder target →
          ContainsGridMinor G target := by
  rcases
      CutMatchingGame.exists_gridVertex_fixedRound_exact_list_halfExpander
    with ⟨cRound, hcRound, hstrategy⟩
  refine ⟨cRound, hcRound, ?_⟩
  intro V _ _ G ell w coordinateOrder target _ P hdegree hq hpow
    htarget hlength hwidth hbudget
  apply gridMinor_of_strongPathOfSetsSystem_of_fixedStrategyV2
    (cRound := cRound) (responseConstant := responseConstant)
    (reserve := reserve) (coordinateOrder := coordinateOrder)
    (target := target)
    (hstrategy := hstrategy hq hpow)
    hclean hcRound hc hreserve P hdegree hq hpow htarget
    hlength hwidth hbudget

/-- Weak-system V2 consumer.  The established strongification and its factor
`20000` are unchanged. -/
theorem gridMinor_of_weakPathOfSetsSystem_of_fixedStrategyV2
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {ell w cRound responseConstant reserve coordinateOrder target : ℕ}
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
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve)
    (P : WeakPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4)
    (hq : 2 ≤ coordinateOrder)
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder)
    (htarget : target ≤ coordinateOrder)
    (hlength :
      cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤ ell)
    (hwidth :
      20000 * (reserve * coordinateOrder ^ 2) ≤ w)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target) :
    ContainsGridMinor G target := by
  let D :=
    Section4Assembly.strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
      P hdegree
  let Pstrong :
      StrongPathOfSetsSystem G ell
        (Section4Assembly.strongifiedWidth w) :=
    Section46.strong_pathOfSetsSystem_of_strongificationData P D
  have hretained :
      reserve * coordinateOrder ^ 2 ≤
        Section4Assembly.strongifiedWidth w := by
    apply Nat.le_of_mul_le_mul_left
      (hwidth.trans
        (Section4Assembly.strongification_width_bound P))
      (by norm_num : 0 < 20000)
  exact
    gridMinor_of_strongPathOfSetsSystem_of_fixedStrategyV2
      hstrategy hclean hcRound hc hreserve Pstrong hdegree
      hq hpow htarget hlength hretained hbudget

end CutResponder
end Exponent7
end SimpleGraph
