import «statements-and-proofs».Exponent7.CutResponder.CutResponderSection5Grid
import «statements-and-proofs».Exponent7.NumericalBounds

/-!
# Exact cut-responder length and local-threshold arithmetic

The strong-system consumer uses `O(log^2 coordinateOrder)` clusters.  This
module proves the corresponding division-free natural-number inequalities and
the explicit Theorem 8.1 target budget.  The final local pseudo-grid bound is
stated before any relation between the pseudo-grid and coordinate scales is
chosen.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

/-- For a power-of-two coordinate order, the exact fresh-cluster length has
the expected product of the round and peeling logarithms. -/
theorem cutResponderStrongLength_eq_of_isPowerOfTwo
    {cRound responseConstant coordinateOrder : ℕ}
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder) :
    cutResponderStrongLength
        cRound responseConstant coordinateOrder =
      (cRound * Nat.log 2 coordinateOrder) *
        (responseConstant *
          (2 * Nat.log 2 coordinateOrder + 1)) := by
  simp only [cutResponderStrongLength, cutResponderRoundBound,
    matchingBatchBudget]
  rw [show
      Nat.log 2 (coordinateOrder ^ 2) =
        2 * Nat.log 2 coordinateOrder by
      rcases hpow with ⟨r, rfl⟩
      rw [← Nat.pow_mul]
      simp [Nat.log_pow (by decide : 1 < 2)]
      omega]

/-- Coarse but exact quadratic-logarithmic cluster budget. -/
theorem cutResponderStrongLength_le
    {cRound responseConstant coordinateOrder : ℕ}
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder) :
    cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤
      3 * cRound * responseConstant *
        (Nat.log 2 coordinateOrder + 1) ^ 2 := by
  let L := Nat.log 2 coordinateOrder
  rw [cutResponderStrongLength_eq_of_isPowerOfTwo hpow]
  have hlinear : 2 * L + 1 ≤ 3 * (L + 1) := by omega
  calc
    (cRound * L) * (responseConstant * (2 * L + 1))
        ≤
      (cRound * L) * (responseConstant * (3 * (L + 1))) := by
        gcongr
    _ ≤
      (cRound * (L + 1)) *
        (responseConstant * (3 * (L + 1))) := by
        gcongr <;> omega
    _ =
      3 * cRound * responseConstant * (L + 1) ^ 2 := by
        ring

theorem cutResponderStrongLength_pos
    {cRound responseConstant coordinateOrder : ℕ}
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hq : 2 ≤ coordinateOrder) :
    0 <
      cutResponderStrongLength
        cRound responseConstant coordinateOrder := by
  simp only [cutResponderStrongLength, matchingBatchBudget]
  exact Nat.mul_pos
    (cutResponderRoundBound_pos hcRound hq)
    (Nat.mul_pos hc (by omega))

/-- The same explicit denominator used by the existing fixed-round expander
arithmetic. -/
def cutResponderTargetDenominator
    (cRound coordinateOrder : ℕ) : ℕ :=
  _root_.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound *
    (Nat.log 2 coordinateOrder) ^ 2

/- If the coordinate order pays the denominator times the requested target,
then the exact Theorem 8.1 target budget holds. -/
set_option maxHeartbeats 800000 in
theorem cutResponderTargetBudget_of_mul_le
    {cRound coordinateOrder target : ℕ}
    (hq : 2 ≤ coordinateOrder)
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder)
    (htarget : 2 ≤ target)
    (hscaled :
      cutResponderTargetDenominator cRound coordinateOrder *
          target ≤
        coordinateOrder) :
    CutResponderTargetBudget cRound coordinateOrder target := by
  let L := Nat.log 2 coordinateOrder
  let denom := cutResponderTargetDenominator cRound coordinateOrder
  have hdenomPos : 0 < denom := by
    have hLpos : 0 < L := by
      simpa [L] using Nat.log_pos (by decide : 1 < 2) hq
    exact Nat.mul_pos
      (_root_.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
        cRound)
      (Nat.pow_pos hLpos)
  have hdenomLt : denom < coordinateOrder := by
    have htwo :
        denom * 2 ≤ coordinateOrder :=
      (Nat.mul_le_mul_left denom htarget).trans hscaled
    omega
  have hdenomSquare :
      4 *
          (((3 *
              (24 *
                _root_.SimpleGraph.HairyCrossbarGrid.largeCaseRoundBound
                  cRound coordinateOrder + 1) *
              (15 *
                (24 *
                  _root_.SimpleGraph.HairyCrossbarGrid.largeCaseRoundBound
                    cRound coordinateOrder + 1))) *
              8) *
            5 *
            Nat.log 2
              (Fintype.card (GridVertex coordinateOrder))) ≤
        denom ^ 2 := by
    simpa [
      _root_.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderDenominatorSquareBudgetProvider,
      denom, cutResponderTargetDenominator, L] using
      (_root_.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderDenominatorSquareBudgetProvider_explicit
        cRound hq hpow hdenomLt)
  have hprod :
      denom * target ≤ 2 * coordinateOrder :=
    hscaled.trans (by omega)
  have hbudget :=
    target_budget_of_denominator_square
      (g := coordinateOrder) (denom := denom) (g' := target)
      (targetScale :=
        cutResponderExpanderScale cRound coordinateOrder)
      (logCard :=
        Nat.log 2 (Fintype.card (GridVertex coordinateOrder)))
      hprod
      (by
        simpa [cutResponderExpanderScale, cutResponderRoundBound,
          _root_.SimpleGraph.HairyCrossbarGrid.largeCaseRoundBound] using
            hdenomSquare)
  have hlog :
      Nat.log 2 (Fintype.card (GridVertex coordinateOrder)) =
        2 * Nat.log 2 coordinateOrder :=
    log_card_gridVertex_of_isPowerOfTwo hpow
  rw [hlog] at hbudget
  simpa [CutResponderTargetBudget] using hbudget

/-- Exact local threshold after substituting the quadratic-logarithmic
strong-system length. -/
def cutResponderLocalThreshold
    (pseudoScale cRound responseConstant coordinateOrder : ℕ) : ℕ :=
  exponentSevenLocalThreshold pseudoScale
    (cutResponderStrongLength
      cRound responseConstant coordinateOrder)

/-- The complete local pseudo-grid threshold has polynomial part
`pseudoScale^6`; all dependence on the cut-matching coordinate order is
polylogarithmic. -/
theorem cutResponderLocalThreshold_le
    {pseudoScale cRound responseConstant coordinateOrder : ℕ}
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hcoordinate : 2 ≤ coordinateOrder)
    (hpow : CrossbarContract.IsPowerOfTwo coordinateOrder) :
    cutResponderLocalThreshold
        pseudoScale cRound responseConstant coordinateOrder ≤
      (2 ^ 39) * cRound * responseConstant *
        pseudoScale ^ 6 *
        (Nat.log 2 coordinateOrder + 1) ^ 2 *
        (Nat.log 2 pseudoScale + 1) ^ 3 := by
  let ell :=
    cutResponderStrongLength
      cRound responseConstant coordinateOrder
  have hell : 0 < ell := by
    exact cutResponderStrongLength_pos hcRound hc hcoordinate
  have hlength :
      ell ≤
        3 * cRound * responseConstant *
          (Nat.log 2 coordinateOrder + 1) ^ 2 := by
    exact cutResponderStrongLength_le hpow
  calc
    cutResponderLocalThreshold
        pseudoScale cRound responseConstant coordinateOrder
        =
      exponentSevenLocalThreshold pseudoScale ell := rfl
    _ ≤
      exponentSevenLocalConstant * pseudoScale ^ 6 * ell *
        (Nat.log 2 pseudoScale + 1) ^ 3 :=
      exponentSevenLocalThreshold_le hell
    _ ≤
      exponentSevenLocalConstant * pseudoScale ^ 6 *
          (3 * cRound * responseConstant *
            (Nat.log 2 coordinateOrder + 1) ^ 2) *
        (Nat.log 2 pseudoScale + 1) ^ 3 := by
      gcongr
    _ ≤
      (2 ^ 39) * cRound * responseConstant *
        pseudoScale ^ 6 *
        (Nat.log 2 coordinateOrder + 1) ^ 2 *
        (Nat.log 2 pseudoScale + 1) ^ 3 := by
      have hcoeff :
          3 * exponentSevenLocalConstant ≤ 2 ^ 39 := by
        norm_num [exponentSevenLocalConstant]
      calc
        exponentSevenLocalConstant * pseudoScale ^ 6 *
              (3 * cRound * responseConstant *
                (Nat.log 2 coordinateOrder + 1) ^ 2) *
            (Nat.log 2 pseudoScale + 1) ^ 3
            =
          (3 * exponentSevenLocalConstant) *
            cRound * responseConstant * pseudoScale ^ 6 *
            (Nat.log 2 coordinateOrder + 1) ^ 2 *
            (Nat.log 2 pseudoScale + 1) ^ 3 := by
              ring
        _ ≤
          (2 ^ 39) * cRound * responseConstant *
            pseudoScale ^ 6 *
            (Nat.log 2 coordinateOrder + 1) ^ 2 *
            (Nat.log 2 pseudoScale + 1) ^ 3 := by
              gcongr

end CutResponder
end Exponent7
end SimpleGraph
