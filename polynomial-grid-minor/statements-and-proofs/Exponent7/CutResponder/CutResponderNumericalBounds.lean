import «statements-and-proofs».Exponent7.CutResponder.CutResponderGlobalDichotomy
import «statements-and-proofs».Exponent7.CutResponder.CutResponderArithmetic
import «statements-and-proofs».GridMinorArithmetic

/-!
# Numerical bounds for the clean active cut-responder pipeline

The cut-matching coordinate order and the pseudo-grid order are rounded
separately.  This file proves the exact local-width and hairy-system bounds
before choosing either unrounded scale.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

/-- Unrounded local width for separate pseudo-grid and cut-matching scales. -/
def cleanResponderNormalizedLocalThreshold
    (pseudoBase coordinateBase cRound responseConstant : ℕ) : ℕ :=
  (2 ^ 39) * cRound * responseConstant *
    pseudoBase ^ 6 *
    (Nat.log 2 coordinateBase + 1) ^ 2 *
    (Nat.log 2 pseudoBase + 1) ^ 3

/-- Rounding both internal scales down preserves the normalized local-width
bound. -/
theorem rounded_cutResponderLocalThreshold_le
    {pseudoBase coordinateBase cRound responseConstant : ℕ}
    (hpseudoBase : 2 ≤ pseudoBase)
    (hcoordinateBase : 2 ≤ coordinateBase)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant) :
    cutResponderLocalThreshold
        (GridMinorArithmetic.powTwoFloor pseudoBase)
        cRound responseConstant
        (GridMinorArithmetic.powTwoFloor coordinateBase) ≤
      cleanResponderNormalizedLocalThreshold
        pseudoBase coordinateBase cRound responseConstant := by
  let pseudoScale :=
    GridMinorArithmetic.powTwoFloor pseudoBase
  let coordinateOrder :=
    GridMinorArithmetic.powTwoFloor coordinateBase
  have hpseudoLe : pseudoScale ≤ pseudoBase :=
    GridMinorArithmetic.powTwoFloor_le_self hpseudoBase
  have hcoordinate :
      2 ≤ coordinateOrder :=
    GridMinorArithmetic.two_le_powTwoFloor hcoordinateBase
  have hcoordinatePow :
      CrossbarContract.IsPowerOfTwo coordinateOrder :=
    GridMinorArithmetic.isPowerOfTwo_powTwoFloor coordinateBase
  have hlogCoordinate :
      Nat.log 2 coordinateOrder + 1 ≤
        Nat.log 2 coordinateBase + 1 :=
    Nat.add_le_add_right
      (GridMinorArithmetic.log_powTwoFloor_le_log
        hcoordinateBase) 1
  have hlogPseudo :
      Nat.log 2 pseudoScale + 1 ≤
        Nat.log 2 pseudoBase + 1 :=
    Nat.add_le_add_right
      (GridMinorArithmetic.log_powTwoFloor_le_log
        hpseudoBase) 1
  calc
    cutResponderLocalThreshold
        pseudoScale cRound responseConstant coordinateOrder
        ≤
      (2 ^ 39) * cRound * responseConstant *
        pseudoScale ^ 6 *
        (Nat.log 2 coordinateOrder + 1) ^ 2 *
        (Nat.log 2 pseudoScale + 1) ^ 3 :=
      cutResponderLocalThreshold_le
        hcRound hc hcoordinate hcoordinatePow
    _ ≤
      (2 ^ 39) * cRound * responseConstant *
        pseudoBase ^ 6 *
        (Nat.log 2 coordinateBase + 1) ^ 2 *
        (Nat.log 2 pseudoBase + 1) ^ 3 := by
      gcongr
    _ =
      cleanResponderNormalizedLocalThreshold
        pseudoBase coordinateBase cRound responseConstant := rfl

/-- The normalized local threshold is nontrivial. -/
theorem cleanResponderNormalizedLocalThreshold_gt_one
    {pseudoBase coordinateBase cRound responseConstant : ℕ}
    (hpseudoBase : 2 ≤ pseudoBase)
    (hcoordinateBase : 2 ≤ coordinateBase)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant) :
    1 <
      cleanResponderNormalizedLocalThreshold
        pseudoBase coordinateBase cRound responseConstant := by
  have hpseudoPow : 2 ≤ pseudoBase ^ 6 := by
    calc
      2 ≤ 2 ^ 6 := by decide
      _ ≤ pseudoBase ^ 6 :=
        Nat.pow_le_pow_left hpseudoBase 6
  have hcoordLog :
      1 ≤ (Nat.log 2 coordinateBase + 1) ^ 2 :=
    Nat.one_le_pow 2 _ (by omega)
  have hpseudoLog :
      1 ≤ (Nat.log 2 pseudoBase + 1) ^ 3 :=
    Nat.one_le_pow 3 _ (by omega)
  have :
      2 ≤
        (2 ^ 39) * cRound * responseConstant *
          pseudoBase ^ 6 *
          (Nat.log 2 coordinateBase + 1) ^ 2 *
          (Nat.log 2 pseudoBase + 1) ^ 3 := by
    calc
      2 = 1 * 1 * 1 * 2 * 1 * 1 := by norm_num
      _ ≤
        (2 ^ 39) * cRound * responseConstant *
          pseudoBase ^ 6 *
          (Nat.log 2 coordinateBase + 1) ^ 2 *
          (Nat.log 2 pseudoBase + 1) ^ 3 := by
        gcongr <;> omega
  simpa [cleanResponderNormalizedLocalThreshold] using this

/-- The normalized local width dominates the rounded pseudo-grid width. -/
theorem powTwoFloor_pseudo_sq_le_cleanResponderNormalized
    {pseudoBase coordinateBase cRound responseConstant : ℕ}
    (hpseudoBase : 2 ≤ pseudoBase)
    (hcoordinateBase : 2 ≤ coordinateBase)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant) :
    (GridMinorArithmetic.powTwoFloor pseudoBase) ^ 2 ≤
      cleanResponderNormalizedLocalThreshold
        pseudoBase coordinateBase cRound responseConstant := by
  have hfloor :
      (GridMinorArithmetic.powTwoFloor pseudoBase) ^ 2 ≤
        pseudoBase ^ 2 :=
    GridMinorArithmetic.pow_powTwoFloor_le_pow hpseudoBase
  have hpow : pseudoBase ^ 2 ≤ pseudoBase ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hrest :
      1 ≤
        (2 ^ 39) * cRound * responseConstant *
          (Nat.log 2 coordinateBase + 1) ^ 2 *
          (Nat.log 2 pseudoBase + 1) ^ 3 := by
    have :
        0 <
          (2 ^ 39) * cRound * responseConstant *
            (Nat.log 2 coordinateBase + 1) ^ 2 *
            (Nat.log 2 pseudoBase + 1) ^ 3 := by
      positivity
    omega
  calc
    (GridMinorArithmetic.powTwoFloor pseudoBase) ^ 2
        ≤ pseudoBase ^ 2 := hfloor
    _ ≤ pseudoBase ^ 6 := hpow
    _ ≤
      (2 ^ 39) * cRound * responseConstant *
        pseudoBase ^ 6 *
        (Nat.log 2 coordinateBase + 1) ^ 2 *
        (Nat.log 2 pseudoBase + 1) ^ 3 := by
      have hmul := Nat.le_mul_of_pos_left
        (pseudoBase ^ 6) hrest
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ =
      cleanResponderNormalizedLocalThreshold
        pseudoBase coordinateBase cRound responseConstant := rfl

/-- Constant in the normalized hairy-system size estimate. -/
def cleanResponderHairyConstant
    (cHair cGrid cRound responseConstant : ℕ) : ℕ :=
  cHair * (2 ^ 39) * cRound * responseConstant *
    (max 2 cGrid) ^ 50

/-- The normalized local width and the standard outer hairy-system length
have polynomial part `pseudoBase^6`. -/
theorem cleanResponder_hairy_size_le_normalized
    (cHair cHairLog cGrid cRound responseConstant
      k pseudoBase coordinateBase : ℕ)
    (hpseudoBase : 2 ≤ pseudoBase) :
    cHair *
        cleanResponderNormalizedLocalThreshold
          pseudoBase coordinateBase cRound responseConstant *
        (PolynomialGridMinor.lengthScale
          cGrid pseudoBase) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        pseudoBase ^ 6 *
        (Nat.log 2 coordinateBase + 1) ^ 2 *
        (Nat.log 2 pseudoBase + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
  have hell :
      PolynomialGridMinor.lengthScale cGrid pseudoBase ≤
        max 2 cGrid *
          (Nat.log 2 pseudoBase + 1) := by
    calc
      PolynomialGridMinor.lengthScale cGrid pseudoBase
          ≤
        PolynomialGridMinor.coarseLengthScale
          cGrid pseudoBase :=
        PolynomialGridMinor.lengthScale_le_unrounded
          cGrid pseudoBase hpseudoBase
      _ ≤ max 2 cGrid * Nat.log 2 pseudoBase :=
        PolynomialGridMinor.coarseLengthScale_le_logarithmic
          cGrid hpseudoBase
      _ ≤
        max 2 cGrid *
          (Nat.log 2 pseudoBase + 1) :=
        Nat.mul_le_mul_left _
          (Nat.le_add_right _ _)
  calc
    cHair *
        cleanResponderNormalizedLocalThreshold
          pseudoBase coordinateBase cRound responseConstant *
        (PolynomialGridMinor.lengthScale
          cGrid pseudoBase) ^ 50 *
        (Nat.log 2 k) ^ cHairLog
        ≤
      cHair *
        ((2 ^ 39) * cRound * responseConstant *
          pseudoBase ^ 6 *
          (Nat.log 2 coordinateBase + 1) ^ 2 *
          (Nat.log 2 pseudoBase + 1) ^ 3) *
        (max 2 cGrid *
          (Nat.log 2 pseudoBase + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
      simp only [cleanResponderNormalizedLocalThreshold]
      gcongr
    _ =
      cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        pseudoBase ^ 6 *
        (Nat.log 2 coordinateBase + 1) ^ 2 *
        (Nat.log 2 pseudoBase + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
      rw [mul_pow]
      have hpow :
          (Nat.log 2 pseudoBase + 1) ^ 3 *
              (Nat.log 2 pseudoBase + 1) ^ 50 =
            (Nat.log 2 pseudoBase + 1) ^ 53 := by
        rw [← pow_add]
      simp only [cleanResponderHairyConstant]
      calc
        cHair *
              ((2 ^ 39) * cRound * responseConstant *
                pseudoBase ^ 6 *
                (Nat.log 2 coordinateBase + 1) ^ 2 *
                (Nat.log 2 pseudoBase + 1) ^ 3) *
            ((max 2 cGrid) ^ 50 *
              (Nat.log 2 pseudoBase + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog
            =
          (cHair * (2 ^ 39) * cRound *
              responseConstant *
              (max 2 cGrid) ^ 50) *
            pseudoBase ^ 6 *
            (Nat.log 2 coordinateBase + 1) ^ 2 *
            ((Nat.log 2 pseudoBase + 1) ^ 3 *
              (Nat.log 2 pseudoBase + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog := by
          ring
        _ =
          (cHair * (2 ^ 39) * cRound *
              responseConstant *
              (max 2 cGrid) ^ 50) *
            pseudoBase ^ 6 *
            (Nat.log 2 coordinateBase + 1) ^ 2 *
            (Nat.log 2 pseudoBase + 1) ^ 53 *
            (Nat.log 2 k) ^ cHairLog := by
          rw [hpow]

end CutResponder
end Exponent7
end SimpleGraph
