import «statements-and-proofs».Exponent7.CutResponder.FreshClusterGrid
import «statements-and-proofs».Section4Assembly

/-!
# Fixed-round cut-responder grid consumer

This is the parallel replacement for the alternating-matching consumer.  It
keeps three parameters separate:

* `pseudoScale`, whose square is the width of the weak system produced by
  Section 5;
* `coordinateOrder`, whose square is the number of global rows used by the
  cut-matching game;
* `target`, the requested grid order after the explicit Theorem 8.1 loss.

The strong system uses one fresh cluster for each fractional matching batch.
For a fixed adversarial round constant this costs exactly

`(cRound * log_2 coordinateOrder) *
  (responseConstant * (log_2 (coordinateOrder^2) + 1))`

clusters.  No asymptotic statement and no axiom occurs in this module.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- Exact number of adversarial cut-matching rounds. -/
def cutResponderRoundBound (cRound coordinateOrder : ℕ) : ℕ :=
  cRound * Nat.log 2 coordinateOrder

/-- Exact number of fresh strong-system clusters consumed by all rounds. -/
def cutResponderStrongLength
    (cRound responseConstant coordinateOrder : ℕ) : ℕ :=
  cutResponderRoundBound cRound coordinateOrder *
    matchingBatchBudget responseConstant coordinateOrder

/-- The explicit separator scale passed to Theorem 8.1. -/
def cutResponderExpanderScale
    (cRound coordinateOrder : ℕ) : ℕ :=
  (3 * (24 * cutResponderRoundBound cRound coordinateOrder + 1) *
      (15 * (24 * cutResponderRoundBound cRound coordinateOrder + 1))) * 8

/-- Division-free target-size budget for the canonical target grid. -/
def CutResponderTargetBudget
    (cRound coordinateOrder target : ℕ) : Prop :=
  cutResponderExpanderScale cRound coordinateOrder *
      (5 * target ^ 2) *
        (2 * Nat.log 2 coordinateOrder) ≤
    coordinateOrder ^ 2

theorem cutResponderRoundBound_pos
    {cRound coordinateOrder : ℕ}
    (hcRound : 0 < cRound) (hq : 2 ≤ coordinateOrder) :
    0 < cutResponderRoundBound cRound coordinateOrder := by
  exact Nat.mul_pos hcRound
    (Nat.log_pos (by decide : 1 < 2) hq)

/-- The multiplication-only budget implies the exact target predicate used by
Theorem 8.1. -/
theorem targetSmallForHost_of_cutResponderTargetBudget
    {cRound coordinateOrder target : ℕ}
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder)
    [Fintype (gridGraphULift.{0} target).edgeSet]
    (hbudget :
      CutResponderTargetBudget cRound coordinateOrder target) :
    TargetSmallForHost
      (V := GridVertex coordinateOrder)
      (gridGraphULift.{0} target)
      (cutResponderExpanderScale cRound coordinateOrder) := by
  apply targetSmallForHost_gridGraphULift_of_five_mul_sq
  have hlog :
      Nat.log 2 (Fintype.card (GridVertex coordinateOrder)) =
        2 * Nat.log 2 coordinateOrder :=
    log_card_gridVertex_of_isPowerOfTwo hpow
  rw [hlog]
  simpa [CutResponderTargetBudget, card_gridVertex, pow_two] using
    hbudget

/-- A supplied exact-round adversarial strategy turns a sufficiently long and
wide strong path-of-sets system into the requested grid. -/
theorem gridMinor_of_strongPathOfSetsSystem_of_fixedStrategy
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
  apply containsGridMinor_of_freshClusterCutMatching_scaled
    (q := coordinateOrder) (target := target)
    hstrategy hclean hc
    (cutResponderRoundBound_pos hcRound hq)
    hlength P selected hdegree hq htarget hwidth
  exact
    targetSmallForHost_of_cutResponderTargetBudget
      hpow hbudget

/-- The exact adversarial strategy already proved in the repository supplies
the fixed-round hypothesis of the strong-system consumer. -/
theorem exists_roundConstant_gridMinor_of_strongPathOfSetsSystem
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
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
  apply gridMinor_of_strongPathOfSetsSystem_of_fixedStrategy
    (cRound := cRound) (responseConstant := responseConstant)
    (reserve := reserve) (coordinateOrder := coordinateOrder)
    (target := target)
    (hstrategy := hstrategy hq hpow)
    hclean hcRound hc hreserve P hdegree hq hpow htarget
    hlength hwidth hbudget

/-- Parallel weak-system consumer.  The existing Section 4.6 strongification
keeps the length and loses only its explicit factor `20000` in width. -/
theorem gridMinor_of_weakPathOfSetsSystem_of_fixedStrategy
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
    gridMinor_of_strongPathOfSetsSystem_of_fixedStrategy
      hstrategy hclean hcRound hc hreserve Pstrong hdegree
      hq hpow htarget hlength hretained hbudget

end CutResponder
end Exponent7
end SimpleGraph
